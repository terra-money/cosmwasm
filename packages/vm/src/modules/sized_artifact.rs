#[derive(Debug, Clone)]
pub struct SizedArtifact {
    pub artifact: Vec<u8>,
    pub size: usize,
}
