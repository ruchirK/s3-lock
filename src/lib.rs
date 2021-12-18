use std::{error, fmt, sync};

use async_trait::async_trait;

mod mem;

/// An abstraction over a connection to a `String key`->`String value` store.
#[async_trait]
pub trait Storage: Send + 'static {
    /// Returns a reference to the value corresponding to the key.
    async fn get(&self, key: &str) -> Result<Option<String>, Error>;

    /// Inserts a key-value pair into the map.
    ///
    /// Inserts must be atomic.
    async fn set(&mut self, key: &str, value: String) -> Result<(), Error>;

    /// Remove a key from the map.
    ///
    /// Succeeds if the key does not exist.
    ///
    /// Deletes must be atomic.
    async fn delete(&mut self, key: &str) -> Result<(), Error>;

    /// List all of the keys in the map.
    async fn list_keys(&self) -> Result<Vec<String>, Error>;

    /// Close the connection to the key-val store.
    async fn close(&mut self) -> Result<bool, Error>;
}

/// An abstraction over a shared lock built on top of a distributed key-value
/// store.
pub struct StorageLock<S: Storage + Send + 'static> {
    process_id: u64,
    storage: S,
}

impl<S: Storage + Send + 'static> StorageLock<S> {
    pub fn new(process_id: u64, storage: S) -> Self {
        Self {
            process_id,
            storage,
        }
    }

    /// Lock `name`.
    async fn lock(&mut self, name: &str) -> Result<(), Error> {
        let mut round = 0;

        loop {
            // TODO: sleep for a variable amount of time for congestion control.

            // Check if another process wrote to a round > our current round.
            let keys = self.storage.list_keys().await?;
            let prefix = format!("REQUEST-LOCK-{}", name);
            let request_keys: Vec<_> = keys
                .into_iter()
                .filter(|k| k.starts_with(&prefix))
                .map(|k| {
                    let split: Vec<_> = k.split('-').collect();
                    let process_id = split[3].parse::<u64>().expect("TODO");
                    let round = split[4].parse::<u64>().expect("TODO");

                    (round, process_id)
                })
                .collect();

            // We lose the election if at least one other process wrote to a round >
            // our current round counter.

            // We definitively lost if one thread wrote to a round >= 2 AND was the only
            // thread to write to that round. Otherwise, the lock is still up for grabs.
            let lost = {
                // First, update our knowledge of the current round based on what
                // we might have already written down
                for (key_round, key_pid) in request_keys.iter() {
                    if *key_pid == self.process_id && *key_round > round {
                        round = *key_round;
                    }
                }

                let mut max_round = round;
                let mut max_round_count = 1;
                for (key_round, key_pid) in request_keys.iter() {
                    if *key_round > max_round {
                        max_round = *key_round;
                        max_round_count = 1
                    } else if *key_round == max_round {
                        max_round_count += 1;
                    }
                }

                if max_round > round && max_round_count == 1 {
                    true
                } else {
                    false
                }
            };

            // Someone has advanced beyond our current round, so we need to try again later
            if lost {
                continue;
            }

            // Check if we won the last two rounds.
            let won = {
                if round < 2 {
                    // Two rounds have not happened yet, so impossible.
                    false
                } else {
                    let mut won = true;
                    for (key_round, key_pid) in request_keys {
                        // There exists at least one such key that proves we did not win the last
                        // two rounds.
                        if (key_round == round || key_round == round - 1)
                            && key_pid != self.process_id
                        {
                            won = false;
                        }
                    }

                    won
                }
            };

            if won {
                break;
            }

            // Otherwise, try to win the next round.
            round += 1;
            let request_key = format!("REQUEST-LOCK-{}-{}-{}", name, self.process_id, round);
            self.storage.set(&request_key, "true".to_string()).await?;
        }

        Ok(())
    }

    /// Unlock `name`.
    async fn unlock(&mut self, name: &str) -> Result<(), Error> {
        let prefix = format!("REQUEST-LOCK-{}", name);
        let keys = self.storage.list_keys().await?;
        let mut request_keys: Vec<_> = keys
            .into_iter()
            .filter(|k| k.starts_with(&prefix))
            .map(|k| {
                let split: Vec<_> = k.split('-').collect();
                let process = split[3].parse::<u64>().expect("TODO");
                let round = split[4].parse::<u64>().expect("TODO");

                (round, process, k)
            })
            .collect();

        let mut last_round = 0;
        for (key_round, key_pid, _) in request_keys.iter() {
            if *key_pid == self.process_id && *key_round > last_round {
                last_round = *key_round;
            }
        }

        let valid_lock = {
            if last_round < 2 {
                false
            } else {
                let mut valid = true;
                for (key_round, key_pid, _) in request_keys.iter() {
                    if *key_pid != self.process_id && *key_round >= last_round {
                        valid = false;
                        break;
                    }
                }

                valid
            }
        };

        if !valid_lock {
            return Err(Error::from("invalid unlock, don't currently have lock"));
        }

        request_keys.sort();
        for (_, key_pid, key) in request_keys.iter() {
            if *key_pid == self.process_id {
                self.storage.delete(&key).await?;
            }
        }

        Ok(())
    }
}

/// A storage related error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// An unstructured storage related error.
    Unstructured(String),
}

impl error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Unstructured(e) => f.write_str(e),
        }
    }
}

impl From<String> for Error {
    fn from(e: String) -> Self {
        Error::Unstructured(e)
    }
}

impl<'a> From<&'a str> for Error {
    fn from(e: &'a str) -> Self {
        Error::Unstructured(e.into())
    }
}

impl<T> From<sync::PoisonError<T>> for Error {
    fn from(e: sync::PoisonError<T>) -> Self {
        Error::Unstructured(format!("poison: {}", e))
    }
}

#[cfg(test)]
mod tests {
    use std::hint;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;
    use std::thread;
    use std::time::Duration;

    use futures_executor::block_on;

    use crate::{Error, Storage, StorageLock};

    pub async fn lock_impl_test_single_thread<S: Storage>(
        mut lock_impl: StorageLock<S>,
    ) -> Result<(), Error> {
        // Repeatedly lock and unlock the same name.
        for _ in 0..10 {
            lock_impl.lock("foo").await?;
            lock_impl.unlock("foo").await?;
        }

        // Lock multiple names at once
        for i in 0..10 {
            lock_impl.lock(&i.to_string()).await?;
        }

        // Unlock everything we just locked
        for i in 0..10 {
            lock_impl.unlock(&i.to_string()).await?;
        }

        // Repeatedly locking the same name should succeed.
        lock_impl.lock("foo").await?;
        lock_impl.lock("foo").await?;

        // Repeatedly unlocking should fail
        lock_impl.unlock("foo").await?;
        assert!(lock_impl.unlock("foo").await.is_err());

        Ok(())
    }

    pub fn lock_impl_test_multi_thread<S: Storage, F: FnMut() -> Result<StorageLock<S>, Error>>(
        mut new_fn: F,
    ) -> Result<(), Error> {
        let spawned = Arc::new(AtomicUsize::new(0));
        let locked = Arc::new(AtomicUsize::new(0));
        let threads = 7;
        let iterations = 10;
        let mut handles = vec![];

        for _ in 0..threads {
            let mut lock_impl = new_fn()?;
            let locked_clone = locked.clone();
            let spawned_clone = spawned.clone();
            let handle = thread::spawn(move || {
                // Wait for all the workers to be spawned.
                spawned_clone.fetch_add(1, Ordering::SeqCst);
                while spawned_clone.load(Ordering::SeqCst) != threads {
                    hint::spin_loop();
                }
                // Repeatedly lock and unlock the same name.
                for _ in 0..iterations {
                    block_on(lock_impl.lock("foo")).expect("TODO");
                    assert_eq!(locked_clone.fetch_add(1, Ordering::SeqCst), 0);
                    thread::sleep(Duration::from_millis(50));
                    assert_eq!(locked_clone.fetch_sub(1, Ordering::SeqCst), 1);
                    block_on(lock_impl.unlock("foo")).expect("TODO");
                }
            });

            handles.push(handle);
        }

        for handle in handles {
            handle.join().expect("todo fix error");
        }

        Ok(())
    }
}
