use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::thread;
use wasmer::Module;

use super::sized_artifact::{SharedModule, SizedArtifact};
use crate::wasm_backend::make_runtime_store;
use crate::{Checksum, Size, VmResult};

/// An pinned in memory module cache
pub struct PinnedMemoryCache {
    artifacts: HashMap<Checksum, SizedArtifact>,
}

impl PinnedMemoryCache {
    /// Creates a new cache
    pub fn new() -> Self {
        PinnedMemoryCache {
            artifacts: HashMap::new(),
        }
    }

    pub fn store(&mut self, checksum: &Checksum, module: Module) -> VmResult<()> {
        let artifact = module.serialize()?;
        let size = loupe::size_of_val(&module) + loupe::size_of_val(&artifact);

        self.artifacts.insert(
            *checksum,
            SizedArtifact {
                size,
                artifact: Arc::new(artifact),
                shared_module: Arc::new(Mutex::new(SharedModule {
                    module,
                    refreshing: false,
                })),
            },
        );
        Ok(())
    }

    /// Removes a module from the cache
    /// Not found artifacts are silently ignored. Potential integrity errors (wrong checksum) are not checked / enforced
    pub fn remove(&mut self, checksum: &Checksum) -> VmResult<()> {
        self.artifacts.remove(checksum);
        Ok(())
    }

    /// Looks up a module in the cache and creates a new module
    pub fn load(
        &mut self,
        checksum: &Checksum,
        instance_memory_limit: Option<Size>,
    ) -> VmResult<Option<Module>> {
        match self.artifacts.get(checksum) {
            Some(sized_artifact) => {
                let mut shared_module = sized_artifact.shared_module.lock().unwrap();
                let module = shared_module.module.clone();
                if !shared_module.refreshing {
                    (*shared_module).refreshing = true;

                    // make background tread to recreate module from artifact
                    let artifact = sized_artifact.artifact.clone();
                    let shared_module = sized_artifact.shared_module.clone();
                    thread::spawn(move || {
                        let store = make_runtime_store(instance_memory_limit);
                        let module = unsafe { Module::deserialize(&store, &artifact) }.unwrap();

                        // hold lock to replace shared module
                        let mut shared_module = shared_module.lock().unwrap();
                        (*shared_module).refreshing = false;
                        (*shared_module).module = module;
                    });
                }

                Ok(Some(module))
            }
            None => Ok(None),
        }
    }

    /// Returns true if and only if this cache has an entry identified by the given checksum
    pub fn has(&self, checksum: &Checksum) -> bool {
        self.artifacts.contains_key(checksum)
    }

    /// Returns the number of elements in the cache.
    pub fn len(&self) -> usize {
        self.artifacts.len()
    }

    /// Returns cumulative size of all elements in the cache.
    ///
    /// This is based on the values provided with `store`. No actual
    /// memory size is measured here.
    pub fn size(&self) -> usize {
        self.artifacts.iter().map(|(_, module)| module.size).sum()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wasm_backend::compile;
    use crate::Size;
    use wasmer::{imports, Instance as WasmerInstance};
    use wasmer_middlewares::metering::set_remaining_points;

    const TESTING_MEMORY_LIMIT: Option<Size> = Some(Size::mebi(16));
    const TESTING_GAS_LIMIT: u64 = 5_000;

    #[test]
    fn pinned_memory_cache_run() {
        let mut cache = PinnedMemoryCache::new();

        // Create module
        let wasm = wat::parse_str(
            r#"(module
            (type $t0 (func (param i32) (result i32)))
            (func $add_one (export "add_one") (type $t0) (param $p0 i32) (result i32)
                get_local $p0
                i32.const 1
                i32.add)
            )"#,
        )
        .unwrap();
        let checksum = Checksum::generate(&wasm);

        // Module does not exist
        let cache_entry = cache.load(&checksum, TESTING_MEMORY_LIMIT).unwrap();
        assert!(cache_entry.is_none());

        // Compile module
        let original = compile(&wasm, None).unwrap();

        // Ensure original module can be executed
        {
            let instance = WasmerInstance::new(&original, &imports! {}).unwrap();
            set_remaining_points(&instance, TESTING_GAS_LIMIT);
            let add_one = instance.exports.get_function("add_one").unwrap();
            let result = add_one.call(&[42.into()]).unwrap();
            assert_eq!(result[0].unwrap_i32(), 43);
        }

        // Store module
        cache.store(&checksum, original).unwrap();

        // Load module
        let cached = cache
            .load(&checksum, TESTING_MEMORY_LIMIT)
            .unwrap()
            .unwrap();

        // Ensure cached module can be executed
        {
            let instance = WasmerInstance::new(&cached, &imports! {}).unwrap();
            set_remaining_points(&instance, TESTING_GAS_LIMIT);
            let add_one = instance.exports.get_function("add_one").unwrap();
            let result = add_one.call(&[42.into()]).unwrap();
            assert_eq!(result[0].unwrap_i32(), 43);
        }
    }

    #[test]
    fn has_works() {
        let mut cache = PinnedMemoryCache::new();

        // Create module
        let wasm = wat::parse_str(
            r#"(module
            (type $t0 (func (param i32) (result i32)))
            (func $add_one (export "add_one") (type $t0) (param $p0 i32) (result i32)
                get_local $p0
                i32.const 1
                i32.add)
            )"#,
        )
        .unwrap();
        let checksum = Checksum::generate(&wasm);

        assert!(!cache.has(&checksum));

        // Add
        let original = compile(&wasm, None).unwrap();
        cache.store(&checksum, original).unwrap();

        assert!(cache.has(&checksum));

        // Remove
        cache.remove(&checksum).unwrap();

        assert!(!cache.has(&checksum));
    }

    #[test]
    fn len_works() {
        let mut cache = PinnedMemoryCache::new();

        // Create module
        let wasm = wat::parse_str(
            r#"(module
            (type $t0 (func (param i32) (result i32)))
            (func $add_one (export "add_one") (type $t0) (param $p0 i32) (result i32)
                get_local $p0
                i32.const 1
                i32.add)
            )"#,
        )
        .unwrap();
        let checksum = Checksum::generate(&wasm);

        assert_eq!(cache.len(), 0);

        // Add
        let original = compile(&wasm, None).unwrap();
        cache.store(&checksum, original).unwrap();

        assert_eq!(cache.len(), 1);

        // Remove
        cache.remove(&checksum).unwrap();

        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn size_works() {
        let mut cache = PinnedMemoryCache::new();

        // Create module
        let wasm1 = wat::parse_str(
            r#"(module
            (type $t0 (func (param i32) (result i32)))
            (func $add_one (export "add_one") (type $t0) (param $p0 i32) (result i32)
                get_local $p0
                i32.const 1
                i32.add)
            )"#,
        )
        .unwrap();
        let checksum1 = Checksum::generate(&wasm1);
        let wasm2 = wat::parse_str(
            r#"(module
            (type $t0 (func (param i32) (result i32)))
            (func $add_one (export "add_two") (type $t0) (param $p0 i32) (result i32)
                get_local $p0
                i32.const 2
                i32.add)
            )"#,
        )
        .unwrap();
        let checksum2 = Checksum::generate(&wasm2);

        assert_eq!(cache.size(), 0);

        // Add 1
        // Add 1
        let module1 = compile(&wasm1, None).unwrap();
        let module1_size =
            loupe::size_of_val(&module1) + loupe::size_of_val(&module1.serialize().unwrap());
        cache.store(&checksum1, module1).unwrap();
        assert_eq!(cache.size(), module1_size);

        // Add 2
        let module2 = compile(&wasm2, None).unwrap();
        let module2_size =
            loupe::size_of_val(&module2) + loupe::size_of_val(&module2.serialize().unwrap());
        cache.store(&checksum2, module2).unwrap();
        assert_eq!(cache.size(), module2_size + module1_size);

        // Remove 1
        cache.remove(&checksum1).unwrap();
        assert_eq!(cache.size(), module2_size);

        // Remove 2
        cache.remove(&checksum2).unwrap();
        assert_eq!(cache.size(), 0);
    }
}
