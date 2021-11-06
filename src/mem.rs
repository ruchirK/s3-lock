use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use async_trait::async_trait;

use crate::{Error, Storage};

/// In-memory implementation of [Storage] for testing purposes.
#[derive(Clone, Debug, Default)]
struct MemStorage {
    data: Arc<Mutex<HashMap<String, String>>>,
}

#[async_trait]
impl Storage for MemStorage {
    async fn get(&self, key: &str) -> Result<Option<String>, Error> {
        Ok(self.data.lock()?.get(key).cloned())
    }

    async fn set(&mut self, key: &str, value: String) -> Result<(), Error> {
        self.data.lock()?.insert(key.to_string(), value);

        Ok(())
    }

    async fn delete(&mut self, key: &str) -> Result<(), Error> {
        self.data.lock()?.remove(key);

        Ok(())
    }

    async fn list_keys(&self) -> Result<Vec<String>, Error> {
        Ok(self.data.lock()?.keys().cloned().collect())
    }

    async fn close(&mut self) -> Result<bool, Error> {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::{lock_impl_test_multi_thread, lock_impl_test_single_thread};
    use crate::{Error, Storage, StorageLock};

    #[tokio::test]
    async fn mem_lock_single_thread() -> Result<(), Error> {
        let mem_storage: MemStorage = MemStorage::default();
        let storage_lock: StorageLock<MemStorage> = StorageLock::new(1, mem_storage);

        lock_impl_test_single_thread(storage_lock).await
    }

    #[test]
    fn mem_lock_multi_thread() -> Result<(), Error> {
        let mem_storage: MemStorage = MemStorage::default();
        let mut pid = 0;

        lock_impl_test_multi_thread(|| {
            let storage_lock = StorageLock::new(pid, mem_storage.clone());
            pid += 1;

            Ok(storage_lock)
        })
    }
}
