// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Advanced parallelism infrastructure

use crate::hashmap::{HashMap, HashSet};
use std::collections::BTreeMap;
use std::hash::Hash;
use std::sync::Mutex;

use std::thread::{self, Scope};

/// A set of tasks for parallel execution, ordered by priority.
pub struct PriorityTasks<P: Ord + Clone, T: Eq + Hash> {
    tasks: BTreeMap<P, HashSet<T>>,
    total_inserted: usize,
}

impl<P: Ord + Clone, T: Eq + Hash> PriorityTasks<P, T> {
    /// Create an empty set of tasks.
    pub fn new() -> Self {
        Self {
            tasks: BTreeMap::new(),
            total_inserted: 0,
        }
    }

    /// Return the number of remaining tasks.
    pub fn len(&self) -> usize {
        self.tasks.values().map(|v| v.len()).sum()
    }

    // Return the total number of tasks inserted.
    pub fn total(&self) -> usize {
        self.total_inserted
    }

    /// Insert a new task with the given priority.
    pub fn insert(&mut self, priority: P, task: T) {
        self.total_inserted += 1;
        if let Some(ts) = self.tasks.get_mut(&priority) {
            ts.insert(task);
        } else {
            self.tasks.insert(priority, HashSet::from_iter([task]));
        }
    }

    /// Get a highest-priority task.
    fn pop(&mut self) -> Option<(P, T)> {
        if let Some(p) = self.tasks.first_key_value().map(|(p, _)| p.clone()) {
            let p_tasks = self.tasks.get_mut(&p).unwrap();
            let t = p_tasks.pop().unwrap();
            if p_tasks.is_empty() {
                self.tasks.remove(&p);
            }
            Some((p, t))
        } else {
            None
        }
    }
}

impl<P: Ord + Clone, T: Eq + Hash> FromIterator<(P, T)> for PriorityTasks<P, T> {
    fn from_iter<I: IntoIterator<Item = (P, T)>>(iter: I) -> Self {
        let mut tasks = Self::new();
        iter.into_iter().for_each(|(p, t)| tasks.insert(p, t));
        tasks
    }
}

/// A manager for prioritized tasks to be executed in parallel.
struct PriorityManager<'a, P, T, R>
where
    P: Ord + Clone,
    T: Eq + Hash,
{
    /// The tasks to be performed.
    tasks: &'a mut PriorityTasks<P, T>,
    /// Running tasks.
    running: HashSet<T>,
    /// Finished tasks and their result.
    results: HashMap<T, R>,
    /// Number of unused threads available for processing.
    unused: usize,
    /// Number of threads currently processing tasks.
    processing: usize,
    /// Whether this batch of tasks has been canceled.
    cancel: bool,
}

impl<'a, P, T, R> PriorityManager<'a, P, T, R>
where
    P: Ord + Clone,
    T: Eq + Hash,
{
    /// Pop a highest-priority task that wasn't seen yet.
    fn pop(&mut self) -> Option<(P, T)> {
        while let Some((p, t)) = self.tasks.pop() {
            if self.unseen(&t) {
                return Some((p, t));
            }
        }

        None
    }

    /// Check whether the given task has been seen (started or executed) yet.
    fn unseen(&self, task: &T) -> bool {
        !self.running.contains(task) && !self.results.contains_key(task)
    }
}

/// The result of a task, consisting of a results type, a vector of new tasks
/// to add to the workload, as well as a `bool` determining whether to cancel (if `true`)
/// the current exection of tasks (by not launching new ones).
type PriorityResult<P, T, R> = (R, Vec<(P, T)>, bool);

/// Available parallelism.
pub fn paralllelism() -> usize {
    std::thread::available_parallelism().unwrap().get()
}

/// A worker able to execute prioritized tasks in parallel.
/// The work closure gets a reference to a taks and its priority,
/// and returns a result in the form of a [`PriorityResult`].
pub struct PriorityWorker<'b, P, T, R, F>
where
    P: Ord + Clone + Send + Sync,
    T: Clone + Eq + Hash + Send + Sync,
    R: Send + Sync,
    F: Fn(&P, &T) -> PriorityResult<P, T, R> + Send + Sync,
{
    dm: Mutex<PriorityManager<'b, P, T, R>>,
    work: F,
}

impl<'b, P, T, R, F> PriorityWorker<'b, P, T, R, F>
where
    P: Ord + Clone + Send + Sync,
    T: Clone + Eq + Hash + Send + Sync,
    R: Send + Sync,
    F: Fn(&P, &T) -> PriorityResult<P, T, R> + Send + Sync,
{
    /// Create a new worker with the given tasks and work closure.
    fn new(tasks: &'b mut PriorityTasks<P, T>, work: F, unused: usize) -> Self {
        Self {
            dm: Mutex::new(PriorityManager {
                tasks,
                running: HashSet::default(),
                results: HashMap::default(),
                unused,
                processing: 0,
                cancel: false,
            }),
            work,
        }
    }

    /// Run a worker with the tasks and work closure.
    /// The work closure gets a reference to a taks and its priority,
    /// and returns a result in the form of a [`PriorityResult`].
    pub fn run(
        tasks: &'b mut PriorityTasks<P, T>,
        work: F,
        mut num_workers: usize,
    ) -> HashMap<T, R> {
        let par_worker = Self::new(tasks, work, num_workers);
        {
            let dm = par_worker.dm.lock().unwrap();
            num_workers = num_workers.min(dm.tasks.len());
        }

        thread::scope(|s| par_worker.launch_workers(num_workers, s));

        let dm = par_worker.dm.into_inner().unwrap();
        dm.results
    }

    /// Run a single-threaded worker which gets the next task and performs it.
    fn worker<'a>(&'a self, s: &'a Scope<'a, '_>) {
        loop {
            let mut task = None;
            {
                let mut dm = self.dm.lock().unwrap();
                dm.unused -= 1;
                if !dm.cancel {
                    task = dm.pop();

                    if let Some((_, t)) = &task {
                        dm.running.insert(t.clone());
                        dm.processing += 1;
                    }
                }
            }

            if task.is_none() {
                return;
            }
            let (p, t) = task.unwrap();
            let (result, new_tasks, cancel) = (self.work)(&p, &t);

            {
                let mut dm = self.dm.lock().unwrap();
                dm.results.insert(t, result);
                for (new_p, new_t) in new_tasks {
                    dm.tasks.insert(new_p, new_t)
                }
                dm.cancel |= cancel;
                dm.processing -= 1;
                if dm.cancel {
                    return;
                } else {
                    dm.unused += 1;
                    let new_workers = (std::thread::available_parallelism().unwrap().get()
                        - dm.unused
                        - dm.processing)
                        .min(dm.tasks.len() - dm.unused);
                    dm.unused += new_workers;
                    self.launch_workers(new_workers, s);
                }
            }
        }
    }

    /// Launch the given number of worker threads in the given [`Scope`].
    fn launch_workers<'a>(&'a self, n: usize, s: &'a Scope<'a, '_>) {
        for _ in 0..n {
            s.spawn(|| self.worker(s));
        }
    }
}
