//! Artifact-bound compiler evidence for dependency static construction.
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};

pub const SCHEMA: u32 = 2;

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Evidence {
    pub schema: u32,
    pub payload_sha256: String,
    pub compiler: String,
    pub target: String,
    pub crate_id: String,
    pub artifact_sha256: String,
    pub origins: Vec<Origin>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Origin {
    pub static_id: String,
    pub kind: OriginKind,
    pub construction: Vec<Construction>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Construction {
    pub definition: String,
    pub kind: OriginKind,
    pub mir_sha256: String,
    pub calls: Vec<String>,
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum OriginKind {
    Declared,
    U32,
}

pub fn sidecar(artifact: &Path) -> PathBuf {
    let mut name = artifact.as_os_str().to_os_string();
    name.push(".miren-origins.json");
    name.into()
}

pub fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

impl Evidence {
    fn payload_digest(&self) -> Result<String, String> {
        serde_json::to_vec(&(
            self.schema,
            &self.compiler,
            &self.target,
            &self.crate_id,
            &self.artifact_sha256,
            &self.origins,
        ))
        .map(|bytes| digest(&bytes))
        .map_err(|error| error.to_string())
    }

    pub fn seal(&mut self) -> Result<(), String> {
        self.payload_sha256 = self.payload_digest()?;
        Ok(())
    }

    pub fn read(
        artifact: &Path,
        compiler: &str,
        target: &str,
        crate_id: &str,
    ) -> Result<Self, String> {
        let bytes = std::fs::read(sidecar(artifact))
            .map_err(|error| format!("dependency static origin evidence unavailable: {error}"))?;
        let evidence: Self = serde_json::from_slice(&bytes)
            .map_err(|error| format!("dependency static origin evidence corrupt: {error}"))?;
        let artifact_bytes = std::fs::read(artifact)
            .map_err(|error| format!("dependency static origin artifact unavailable: {error}"))?;
        if evidence.payload_sha256 != evidence.payload_digest()?
            || evidence.schema != SCHEMA
            || evidence.compiler != compiler
            || evidence.target != target
            || evidence.crate_id != crate_id
            || evidence.artifact_sha256 != digest(&artifact_bytes)
        {
            return Err(
                "dependency static origin evidence does not match compiler artifact".into(),
            );
        }
        Ok(evidence)
    }

    pub fn origin(&self, static_id: &str) -> Option<OriginKind> {
        if !self.certifies(static_id) {
            return None;
        }
        self.origins
            .iter()
            .find(|origin| origin.static_id == static_id)
            .map(|origin| origin.kind)
    }

    pub fn certifies(&self, static_id: &str) -> bool {
        if self.payload_digest().as_ref() != Ok(&self.payload_sha256) {
            return false;
        }
        let matching: Vec<_> = self
            .origins
            .iter()
            .filter(|origin| origin.static_id == static_id)
            .collect();
        let [origin] = matching.as_slice() else {
            return false;
        };
        if origin.construction.is_empty() || origin.construction.len() > 64 {
            return false;
        }
        let nodes: std::collections::BTreeSet<_> = origin
            .construction
            .iter()
            .map(|node| node.definition.as_str())
            .collect();
        nodes.len() == origin.construction.len()
            && nodes.contains(static_id)
            && origin
                .construction
                .iter()
                .find(|node| node.definition == static_id)
                .is_some_and(|node| node.kind == origin.kind)
            && origin.construction.iter().all(|node| {
                node.mir_sha256.len() == 64
                    && node.mir_sha256.bytes().all(|byte| byte.is_ascii_hexdigit())
                    && node
                        .calls
                        .iter()
                        .all(|callee| nodes.contains(callee.as_str()))
            })
    }
}
