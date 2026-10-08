//! Cargo source inputs retained for independent compiler invocation replay.

use std::collections::BTreeMap;

pub fn is_source_environment(name: &str) -> bool {
    matches!(
        name,
        "CARGO_MANIFEST_DIR"
            | "CARGO_MANIFEST_PATH"
            | "CARGO_CRATE_NAME"
            | "CARGO_BIN_NAME"
            | "CARGO_PRIMARY_PACKAGE"
            | "OUT_DIR"
    ) || ["CARGO_PKG_", "CARGO_FEATURE_", "CARGO_CFG_", "DEP_"]
        .iter()
        .any(|prefix| name.starts_with(prefix))
}

pub fn source_environment() -> Option<BTreeMap<String, String>> {
    std::env::vars_os()
        .filter(|(name, _)| name.to_str().is_some_and(is_source_environment))
        .map(|(name, value)| Some((name.into_string().ok()?, value.into_string().ok()?)))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_inputs_exclude_credentials_and_analysis_policies() {
        for name in [
            "CARGO_PKG_VERSION",
            "CARGO_FEATURE_STD",
            "OUT_DIR",
            "DEP_HAL_CONFIG",
        ] {
            assert!(is_source_environment(name));
        }
        for name in [
            "CARGO_REGISTRY_TOKEN",
            "MIREN_STARTUP",
            "RUSTC_WRAPPER",
            "PATH",
        ] {
            assert!(!is_source_environment(name));
        }
    }
}
