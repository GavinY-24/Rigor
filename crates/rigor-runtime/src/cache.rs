//! VerificationKey and interface caches.
//!
//! The verification cache key includes every input relevant to the fact
//! (checker build, profile, policy, evidence closure, covered roots, ticket
//! rule version). The interface cache key is deliberately coarser and may
//! only drive interface-reuse decisions — never validation of a replacement
//! proof (see `rigor_spec::ids::interface_key`).

use crate::receipt::Receipt;
use rigor_spec::{InterfaceKey, VerificationKey};
use std::collections::HashMap;
use std::path::PathBuf;

#[derive(Debug, Default)]
pub struct VerifyCache {
    memory: HashMap<VerificationKey, Receipt>,
    disk_dir: Option<PathBuf>,
}

impl VerifyCache {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_disk(dir: PathBuf) -> Self {
        Self { memory: HashMap::new(), disk_dir: Some(dir) }
    }

    /// Independent verification mode: no cache at all.
    pub fn disabled() -> Self {
        Self { memory: HashMap::new(), disk_dir: None }
    }

    pub fn get(&self, key: &VerificationKey) -> Option<Receipt> {
        if let Some(r) = self.memory.get(key) {
            return Some(r.clone());
        }
        if let Some(dir) = &self.disk_dir {
            let path = dir.join(format!("{}.rigorr.json", key.to_hex()));
            if let Ok(text) = std::fs::read_to_string(&path) {
                if let Some(mut r) = Receipt::from_json(&text) {
                    // Disk receipts are display-grade: mark them by keeping the
                    // key so callers can tell this was a cache hit.
                    r.verification_key = key.to_hex();
                    return Some(r);
                }
            }
        }
        None
    }

    pub fn put(&mut self, key: VerificationKey, receipt: Receipt) {
        if let Some(dir) = &self.disk_dir {
            let _ = std::fs::create_dir_all(dir);
            let path = dir.join(format!("{}.rigorr.json", key.to_hex()));
            let _ = std::fs::write(&path, receipt.to_json());
        }
        self.memory.insert(key, receipt);
    }

    pub fn clear(&mut self) {
        self.memory.clear();
        if let Some(dir) = &self.disk_dir {
            let _ = std::fs::remove_dir_all(dir);
            let _ = std::fs::create_dir_all(dir);
        }
    }

    pub fn len(&self) -> usize {
        self.memory.len()
    }
    pub fn is_empty(&self) -> bool {
        self.memory.is_empty()
    }
}

/// Interface reuse cache: statement-level, used to decide whether downstream
/// interface dependents need re-elaboration after an opaque proof repair.
#[derive(Debug, Default)]
pub struct IfaceCache {
    map: HashMap<InterfaceKey, String>, // key -> verification key hex that validated the interface
}

impl IfaceCache {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn record(&mut self, key: InterfaceKey, verification_key_hex: String) {
        self.map.insert(key, verification_key_hex);
    }
    pub fn lookup(&self, key: &InterfaceKey) -> Option<&String> {
        self.map.get(key)
    }
}
