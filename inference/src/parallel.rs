// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Advanced parallelism infrastructure

use crate::hashmap::HashMap;
use std::collections::VecDeque;
use std::hash::Hash;
use std::sync::Mutex;

use std::thread::{self, Scope};

struct DequeManager<T, R>
where
    T: Eq + Hash,
{
    deque: VecDeque<T>,
    results: HashMap<T, Option<R>>,
    waiting: usize,
    processing: usize,
    cancel: bool,
}

// result, push front, push back, cancel
type DequeResult<T, R> = (R, Vec<T>, Vec<T>, bool);

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
                results: HashMap::default(),
                waiting,
                processing: 0,
                cancel: false,
            }),
            work,
        }
    }

    pub fn run<I: IntoIterator<Item = T>>(tasks: I, work: F) -> HashMap<T, Option<R>> {
        let deque: VecDeque<T> = tasks.into_iter().collect();
        let num_workers = std::thread::available_parallelism()
            .unwrap()
            .get()
            .min(deque.len());
        let par_worker = Self::new(deque, work, num_workers);

        thread::scope(|s| par_worker.launch_workers(num_workers, s));

        par_worker.dm.into_inner().unwrap().results
    }

    fn worker<'a>(&'a self, s: &'a Scope<'a, '_>) {
        loop {
            let mut task = None;
            {
                let mut dm = self.dm.lock().unwrap();
                dm.waiting -= 1;
                if !dm.cancel {
                    task = dm.deque.pop_front();
                    while task.as_ref().is_some_and(|t| dm.results.contains_key(t)) {
                        task = dm.deque.pop_front();
                    }

                    if let Some(t) = &task {
                        dm.results.insert(t.clone(), None);
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
                dm.results.insert(task.unwrap(), Some(result));
                for t in push_front {
                    dm.deque.push_front(t);
                }
                for t in push_back {
                    dm.deque.push_back(t);
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
