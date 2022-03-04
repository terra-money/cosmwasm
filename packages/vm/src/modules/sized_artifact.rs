use std::sync::{Arc, Mutex};
use wasmer::Module;

#[derive(Debug, Clone)]
pub struct SizedArtifact {
    pub shared_module: Arc<Mutex<SharedModule>>,
    pub artifact: Arc<Vec<u8>>,
    pub size: usize,
}

#[derive(Debug, Clone)]
pub struct SharedModule {
    pub module: Module,
    pub refreshing: bool,
}
