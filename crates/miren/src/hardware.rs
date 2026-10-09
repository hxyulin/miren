//! Declarative, explicitly assumed device effects for external host integrations.
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum HardwareDevice {
    #[serde(rename = "stm32h723vg")]
    Stm32h723vg,
    #[serde(rename = "stm32f407ig")]
    Stm32f407ig,
}

impl HardwareDevice {
    pub fn chip(self) -> &'static str {
        match self {
            Self::Stm32h723vg => "stm32h723vg",
            Self::Stm32f407ig => "stm32f407ig",
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MmioRegion {
    pub name: String,
    pub start: u64,
    pub length: u64,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MmioWriteRegister {
    pub name: String,
    pub address: u64,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MmioReadRegister {
    pub name: String,
    pub address: u64,
}

/// Schema 1 admits byte-address transport and exact write-only unsigned 32-bit registers.
/// Schema 2 additionally admits independent arbitrary u32 reads at configured addresses.
/// Neither schema supplies Rust allocation, reference, scheduler or emulator semantics.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct HardwareModel {
    pub schema_version: u32,
    pub device: HardwareDevice,
    pub pointer_bits: u32,
    pub reason: String,
    pub regions: Vec<MmioRegion>,
    pub write_registers: Vec<MmioWriteRegister>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub read_registers: Vec<MmioReadRegister>,
}

impl HardwareModel {
    pub fn new(device: HardwareDevice, pointer_bits: u32, reason: impl Into<String>) -> Self {
        Self {
            schema_version: 1,
            device,
            pointer_bits,
            reason: reason.into(),
            regions: Vec::new(),
            write_registers: Vec::new(),
            read_registers: Vec::new(),
        }
    }

    pub fn with_region(mut self, name: impl Into<String>, start: u64, length: u64) -> Self {
        self.regions.push(MmioRegion {
            name: name.into(),
            start,
            length,
        });
        self
    }

    pub fn with_write_register(mut self, name: impl Into<String>, address: u64) -> Self {
        self.write_registers.push(MmioWriteRegister {
            name: name.into(),
            address,
        });
        self
    }

    pub fn with_read_register(mut self, name: impl Into<String>, address: u64) -> Self {
        self.schema_version = 2;
        self.read_registers.push(MmioReadRegister {
            name: name.into(),
            address,
        });
        self
    }

    /// Canonical report premise. Only actual admitted operations record this assumption.
    pub fn assumption(&self) -> String {
        format!(
            "hardware-model:v{}:device={};pointer_bits={};reason={}",
            self.schema_version,
            self.device.chip(),
            self.pointer_bits,
            self.reason,
        )
    }

    pub fn validate(&self) -> Result<(), String> {
        if !matches!(self.schema_version, 1 | 2) || self.pointer_bits != 32 {
            return Err("hardware model requires schema 1 or 2 and pointer_bits 32".into());
        }
        if self.reason.trim().is_empty() {
            return Err("hardware model requires an explicit nonempty assumption reason".into());
        }
        if !(1..=16).contains(&self.regions.len())
            || self.write_registers.len() > 64
            || self.read_registers.len() > 64
            || (self.write_registers.is_empty() && self.read_registers.is_empty())
            || (self.schema_version == 1 && !self.read_registers.is_empty())
        {
            return Err(
                "hardware model requires bounded registers, regions, and schema 2 for reads".into(),
            );
        }
        let limit = 1_u128 << self.pointer_bits;
        let mut names = BTreeSet::new();
        for region in &self.regions {
            if region.name.trim().is_empty()
                || region.name.trim() != region.name
                || !names.insert(&region.name)
                || !(1..=4096).contains(&region.length)
                || region.start < 0x4000_0000
                || u128::from(region.start) + u128::from(region.length) > 0x6000_0000
                || u128::from(region.start) + u128::from(region.length) > limit
            {
                return Err(
                    "hardware regions need unique names and nonwrapping bounded extents".into(),
                );
            }
        }
        for (index, region) in self.regions.iter().enumerate() {
            let end = u128::from(region.start) + u128::from(region.length);
            if self.regions[..index].iter().any(|other| {
                let other_end = u128::from(other.start) + u128::from(other.length);
                u128::from(region.start) < other_end && u128::from(other.start) < end
            }) {
                return Err("hardware transport regions must not overlap".into());
            }
        }
        names.clear();
        let mut addresses = BTreeSet::new();
        for register in &self.write_registers {
            if register.name.trim().is_empty()
                || register.name.trim() != register.name
                || !names.insert(&register.name)
                || !addresses.insert(register.address)
                || register.address % 4 != 0
                || !self.regions.iter().any(|region| {
                    register.address >= region.start
                        && u128::from(register.address) + 4
                            <= u128::from(region.start) + u128::from(region.length)
                })
            {
                return Err(
                    "hardware write registers need unique aligned contained u32 addresses".into(),
                );
            }
        }
        names.clear();
        addresses.clear();
        for register in &self.read_registers {
            if register.name.trim().is_empty()
                || register.name.trim() != register.name
                || !names.insert(&register.name)
                || !addresses.insert(register.address)
                || register.address % 4 != 0
                || !self.regions.iter().any(|region| {
                    register.address >= region.start
                        && u128::from(register.address) + 4
                            <= u128::from(region.start) + u128::from(region.length)
                })
            {
                return Err(
                    "hardware read registers need unique aligned contained u32 addresses".into(),
                );
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn model() -> HardwareModel {
        HardwareModel::new(
            HardwareDevice::Stm32h723vg,
            32,
            "explicit device access premise",
        )
        .with_region("gpioc", 0x5802_0800, 0x400)
        .with_write_register("bsrr", 0x5802_0818)
    }

    #[test]
    fn public_builder_validates_and_serializes_canonical_premise() {
        let model = model();
        model.validate().unwrap();
        assert_eq!(
            model.assumption(),
            "hardware-model:v1:device=stm32h723vg;pointer_bits=32;reason=explicit device access premise"
        );
        let config = crate::ContractConfig::default().with_hardware(model);
        config.validate().unwrap();
        let json = serde_json::to_value(&config).unwrap();
        assert_eq!(json["hardware"]["device"], "stm32h723vg");
        let config: crate::ContractConfig = serde_json::from_value(json).unwrap();
        config.validate().unwrap();
        let old: crate::ContractConfig =
            serde_json::from_str(r#"{"schema_version":1,"functions":[]}"#).unwrap();
        old.validate().unwrap();
        assert!(serde_json::to_value(old).unwrap().get("hardware").is_none());
    }

    #[test]
    fn device_models_reject_ram_null_wrong_width_and_unbounded_registers() {
        for start in [0, 0x2000_0000, 0x3fff_ffff, 0x6000_0000, u64::MAX] {
            let mut invalid = model();
            invalid.regions[0].start = start;
            assert!(invalid.validate().is_err());
        }
        for bits in [0, 16, 64, 128] {
            let mut invalid = model();
            invalid.pointer_bits = bits;
            assert!(invalid.validate().is_err());
        }
        for address in [0x5802_0819, 0x5802_0c00, 0x2000_0000] {
            let mut invalid = model();
            invalid.write_registers[0].address = address;
            assert!(invalid.validate().is_err());
        }
        let mut invalid = model();
        invalid.regions[0].start = 0x5fff_fffc;
        invalid.regions[0].length = 8;
        assert!(invalid.validate().is_err());
        let mut invalid = model();
        invalid.regions[0].length = 4097;
        assert!(invalid.validate().is_err());
        assert!(
            model()
                .with_region("overlap", 0x5802_0810, 32)
                .validate()
                .is_err()
        );
        assert!(
            model()
                .with_write_register("duplicate", 0x5802_0818)
                .validate()
                .is_err()
        );
        let mut invalid = model();
        invalid.reason.clear();
        assert!(invalid.validate().is_err());
    }
    #[test]
    fn versioned_reads_preserve_v1_bytes_and_validate_directional_access() {
        let legacy = model();
        let json = serde_json::to_value(&legacy).unwrap();
        assert!(json.get("read_registers").is_none());
        let mut reads = legacy.with_read_register("pupdr", 0x5802_080c);
        reads.validate().unwrap();
        assert_eq!(reads.schema_version, 2);
        assert!(reads.assumption().starts_with("hardware-model:v2:"));
        let decoded: HardwareModel =
            serde_json::from_value(serde_json::to_value(&reads).unwrap()).unwrap();
        decoded.validate().unwrap();
        reads.schema_version = 1;
        assert!(reads.validate().is_err());
        reads.schema_version = 2;
        reads.write_registers.clear();
        reads.validate().unwrap();
        assert!(
            reads
                .clone()
                .with_read_register("duplicate", 0x5802_080c)
                .validate()
                .is_err()
        );
        for address in [0x5802_080d, 0x5802_0c00, 0x2000_0000] {
            let mut invalid = reads.clone();
            invalid.read_registers[0].address = address;
            assert!(invalid.validate().is_err());
        }
        reads.read_registers.clear();
        assert!(reads.validate().is_err());
    }
}
