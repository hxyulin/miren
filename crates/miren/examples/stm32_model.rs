#![forbid(unsafe_code)]

use miren::{ContractConfig, HardwareDevice, HardwareModel};

fn main() -> Result<(), String> {
    let (device, name, start) = match std::env::args().nth(1).as_deref() {
        Some("stm32h723vg") => (HardwareDevice::Stm32h723vg, "GPIOC", 0x5802_0800),
        Some("stm32f407ig") => (HardwareDevice::Stm32f407ig, "GPIOH", 0x4002_1c00),
        _ => return Err("usage: stm32_model stm32h723vg|stm32f407ig".into()),
    };
    let mut hardware = HardwareModel::new(
        device,
        32,
        "UNVERIFIED device premise: this GPIO region supports bounded byte address transport and \
         aligned u32 BSRR writes without trapping or modifying tracked Rust storage. No reads, \
         pin observations, clock readiness, interrupt effects or executor progress are modeled.",
    )
    .with_region(name, start, 32)
    .with_write_register(format!("{name}_BSRR"), start + 0x18);
    match std::env::args().nth(2).as_deref() {
        Some("rmw") => {
            for (register, offset) in [("PUPDR", 12), ("OTYPER", 4), ("OSPEEDR", 8), ("MODER", 0)] {
                let name = format!("{name}_{register}");
                hardware = hardware
                    .with_read_register(&name, start + offset)
                    .with_write_register(name, start + offset);
            }
            hardware.reason = "UNVERIFIED GPIO access premise: configured exact u32 reads and \
                writes terminate without trapping or unmodeled Rust storage changes. Each read \
                admits an independent arbitrary word; no readback, stability, hardware readiness \
                or executor progress is assumed."
                .into();
        }
        None => {}
        _ => return Err("optional second argument must be rmw".into()),
    }
    let config = ContractConfig::default().with_hardware(hardware);
    config.validate()?;
    println!(
        "{}",
        serde_json::to_string_pretty(&config).map_err(|error| error.to_string())?
    );
    Ok(())
}
