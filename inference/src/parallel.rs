// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Advanced parallelism infrastructure

use crate::hashmap::{HashMap, HashSet};
use std::collections::VecDeque;
use std::hash::Hash;
use std::sync::Mutex;

use std::thread::{self, Scope};

struct DequeManager<T, R>
where
    T: Eq + Hash,
{
    deque: VecDeque<T>,
    running: HashSet<T>,
    results: HashMap<T, R>,
    waiting: usize,
    processing: usize,
    cancel: bool,
}

// result, push front, push back, cancel
type DequeResult<T, R> = (R, Vec<T>, Vec<T>, bool);

pub fn paralllelism() -> usize {
    std::thread::available_parallelism().unwrap().get()
}

pub struct DequeWorker<T, R, F>
where
    T: Clone + Eq + Hash + Send + Sync,
    R: Send + Sync,
    F: Fn(&T) -> DequeResult<T, R> + Send + Sync,
{
    dm: Mutex<DequeManager<T, R>>,
    work: F,
}

impl<T, R, F> DequeWorker<T, R, F>
where
    T: Clone + Eq + Hash + Send + Sync,
    R: Send + Sync,
    F: Fn(&T) -> DequeResult<T, R> + Send + Sync,
{
    fn new(deque: VecDeque<T>, work: F, waiting: usize) -> Self {
        Self {
            dm: Mutex::new(DequeManager {
                deque,
                running: HashSet::default(),
                results: HashMap::default(),
                waiting,
                processing: 0,
                cancel: false,
            }),
            work,
        }
    }

    pub fn run<I: IntoIterator<Item = T>>(
        tasks: I,
        work: F,
        mut num_workers: usize,
    ) -> (HashMap<T, R>, VecDeque<T>) {
        let deque: VecDeque<T> = tasks.into_iter().collect();
        num_workers = num_workers.min(deque.len());
        let par_worker = Self::new(deque, work, num_workers);

        thread::scope(|s| par_worker.launch_workers(num_workers, s));

        let dm = par_worker.dm.into_inner().unwrap();
        (dm.results, dm.deque)
    }

    fn worker<'a>(&'a self, s: &'a Scope<'a, '_>) {
        loop {
            let mut task = None;
            {
                let mut dm = self.dm.lock().unwrap();
                dm.waiting -= 1;
                if !dm.cancel {
                    task = dm.deque.pop_front();
                    while task.as_ref().is_some_and(|t| dm.running.contains(t)) {
                        task = dm.deque.pop_front();
                    }

                    if let Some(t) = &task {
                        dm.running.insert(t.clone());
                        dm.processing += 1;
                    }
                }
            }

            if task.is_none() {
                return;
            }
            let (result, push_front, push_back, cancel) = (self.work)(task.as_ref().unwrap());

            {
                let mut dm = self.dm.lock().unwrap();
                dm.results.insert(task.unwrap(), result);
                for t in push_front {
                    if !dm.results.contains_key(&t) {
                        dm.deque.push_front(t);
                    }
                }
                for t in push_back {
                    if !dm.results.contains_key(&t) {
                        dm.deque.push_back(t);
                    }
                }
                dm.cancel |= cancel;
                dm.processing -= 1;
                if dm.cancel {
                    return;
                } else {
                    dm.waiting += 1;
                    let new_workers = (std::thread::available_parallelism().unwrap().get()
                        - dm.waiting
                        - dm.processing)
                        .min(dm.deque.len() - dm.waiting);
                    dm.waiting += new_workers;
                    self.launch_workers(new_workers, s);
                }
            }
        }
    }

    fn launch_workers<'a>(&'a self, n: usize, s: &'a Scope<'a, '_>) {
        for _ in 0..n {
            s.spawn(|| self.worker(s));
        }
    }
}
