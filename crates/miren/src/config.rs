use crate::{Contract, ContractKind, ContractStatus};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::path::Path;

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ContractConfig {
    pub schema_version: u32,
    pub functions: Vec<FunctionContract>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub hardware: Option<crate::HardwareModel>,
}

/// Explicit frame premise for an exact selected trusted call, never inferred from reachability.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum TrustedStorageEffect {
    /// No mutation, publication or retirement of pre-existing ordinary tracked storage.
    /// Static/startup state and atomic precision are still invalidated.
    PreserveExistingOrdinaryStorage,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct FunctionContract {
    pub function: String,
    #[serde(default)]
    pub instance: Option<String>,
    #[serde(default)]
    pub arguments: Vec<String>,
    #[serde(default)]
    pub requires: Vec<String>,
    #[serde(default)]
    pub ensures: Vec<String>,
    #[serde(default)]
    pub trusted: bool,
    #[serde(default)]
    pub no_panic: bool,
    #[serde(default)]
    pub modifies: Option<Vec<String>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub storage_effect: Option<TrustedStorageEffect>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub returns_alias: Option<String>,
    #[serde(default)]
    pub reason: Option<String>,
}

impl Default for ContractConfig {
    fn default() -> Self {
        Self {
            schema_version: 1,
            functions: Vec::new(),
            hardware: None,
        }
    }
}

impl ContractConfig {
    pub fn with_hardware(mut self, hardware: crate::HardwareModel) -> Self {
        self.hardware = Some(hardware);
        self
    }

    pub fn read(path: &Path) -> Result<Self, String> {
        let bytes = std::fs::read(path)
            .map_err(|error| format!("contracts {}: {error}", path.display()))?;
        let config: Self = serde_json::from_slice(&bytes)
            .map_err(|error| format!("contracts {}: {error}", path.display()))?;
        config.validate()?;
        Ok(config)
    }

    pub fn validate(&self) -> Result<(), String> {
        if self.schema_version != 1 {
            return Err("contract configuration needs schema_version 1".to_owned());
        }
        let mut selectors = BTreeSet::new();
        if let Some(hardware) = &self.hardware {
            hardware.validate()?;
        }
        for function in &self.functions {
            if !function.function.contains("::")
                || function.function.trim() != function.function
                || function.function.contains('*')
                || function.function.contains('?')
            {
                return Err("contract functions require exact crate-qualified paths".to_owned());
            }
            if !selectors.insert((&function.function, &function.instance)) {
                return Err("duplicate function/instance contract selector".to_owned());
            }
            let mut names = BTreeSet::new();
            for name in &function.arguments {
                if syn::parse_str::<syn::Ident>(name).is_err()
                    || name == "result"
                    || name.starts_with("final_")
                    || !names.insert(name)
                {
                    return Err(
                        "argument aliases must be unique, unreserved identifiers".to_owned()
                    );
                }
            }
            for predicate in function.requires.iter().chain(&function.ensures) {
                syn::parse_str::<syn::Expr>(predicate)
                    .map_err(|error| format!("invalid contract predicate: {error}"))?;
            }
            if function.storage_effect.is_some()
                && (!function.trusted
                    || function.modifies.is_some()
                    || function.returns_alias.is_some())
            {
                return Err(concat!(
                    "storage_effect requires trusted=true and ",
                    "conflicts with modifies or returns_alias"
                )
                .into());
            }
            if function.trusted {
                if !function.no_panic
                    || function
                        .reason
                        .as_ref()
                        .is_none_or(|reason| reason.trim().is_empty())
                {
                    return Err(
                        "trusted functions require no_panic=true and a nonempty reason".to_owned(),
                    );
                }
                if let Some(modifies) = &function.modifies
                    && modifies
                        .iter()
                        .any(|name| !function.arguments.contains(name))
                {
                    return Err("modifies must name declared positional arguments".to_owned());
                }
                if let Some(name) = &function.returns_alias
                    && !function.arguments.contains(name)
                {
                    return Err("returns_alias must name a declared positional argument".to_owned());
                }
            } else if function.modifies.is_some()
                || function.returns_alias.is_some()
                || function.reason.is_some()
            {
                return Err(
                    "effects, return aliases and reasons apply only to trusted summaries"
                        .to_owned(),
                );
            }
        }
        Ok(())
    }
}

impl FunctionContract {
    pub fn selector(&self) -> String {
        self.instance.as_ref().map_or_else(
            || self.function.clone(),
            |instance| format!("{} {instance}", self.function),
        )
    }
    /// Canonical premise recorded only when this selected trusted effect is actually used.
    pub fn storage_assumption(&self) -> Option<String> {
        self.storage_effect.map(|effect| {
            let effect = match effect {
                TrustedStorageEffect::PreserveExistingOrdinaryStorage => {
                    "preserve_existing_ordinary_storage"
                }
            };
            format!(
                "trusted-storage:v1:selector={};effect={effect};reason={}",
                self.selector(),
                self.reason.as_deref().unwrap_or_default()
            )
        })
    }

    pub fn metadata(&self) -> Vec<Contract> {
        let mut result = Vec::new();
        if self.no_panic {
            result.push(Contract {
                kind: ContractKind::NoPanic,
                predicate: None,
                status: ContractStatus::PendingVerification,
            });
        }
        for (kind, predicates) in [
            (ContractKind::Requires, &self.requires),
            (ContractKind::Ensures, &self.ensures),
        ] {
            for predicate in predicates {
                result.push(Contract {
                    kind: kind.clone(),
                    predicate: Some(predicate.clone()),
                    status: ContractStatus::PendingVerification,
                });
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn explicit_storage_effect_is_versioned_reported_and_excludes_conflicting_effects() {
        let legacy = serde_json::json!({ "schema_version":1, "functions":[{
            "function":"fixture::init", "trusted":true, "no_panic":true,
            "reason":"no mutation, publication or retirement of pre-existing ordinary storage"
        }] });
        let config: ContractConfig = serde_json::from_value(legacy.clone()).unwrap();
        config.validate().unwrap();
        assert!(config.functions[0].storage_assumption().is_none());
        assert!(
            serde_json::to_value(config).unwrap()["functions"][0]
                .get("storage_effect")
                .is_none()
        );
        let mut opt_in = legacy.clone();
        opt_in["functions"][0]["storage_effect"] =
            serde_json::json!("preserve_existing_ordinary_storage");
        let config: ContractConfig = serde_json::from_value(opt_in.clone()).unwrap();
        config.validate().unwrap();
        assert_eq!(
            config.functions[0].storage_assumption().unwrap(),
            concat!(
                "trusted-storage:v1:selector=fixture::init;",
                "effect=preserve_existing_ordinary_storage;",
                "reason=no mutation, publication or retirement of pre-existing ordinary storage"
            )
        );
        let mut instance = config.clone();
        instance.functions[0].instance = Some("[u32]".into());
        assert!(
            instance.functions[0]
                .storage_assumption()
                .unwrap()
                .contains("selector=fixture::init [u32];")
        );
        for (field, value) in [
            ("modifies", serde_json::json!([])),
            ("returns_alias", serde_json::json!("arg0")),
            ("trusted", serde_json::json!(false)),
            ("reason", serde_json::json!("")),
            ("no_panic", serde_json::json!(false)),
        ] {
            let mut invalid = opt_in.clone();
            invalid["functions"][0][field] = value;
            let config: ContractConfig = serde_json::from_value(invalid).unwrap();
            assert!(config.validate().is_err(), "{field}");
        }
        opt_in["functions"][0]["storage_effect"] = serde_json::json!("preserve_everything");
        assert!(serde_json::from_value::<ContractConfig>(opt_in).is_err());
    }
}
