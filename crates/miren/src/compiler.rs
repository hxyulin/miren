#![forbid(unsafe_code)]

use std::io::Write;
use std::process::{Command, ExitCode};

fn run() -> Result<ExitCode, Box<dyn std::error::Error>> {
    let mut args = std::env::args_os().skip(1);
    let compiler = args
        .next()
        .ok_or("expected a compiler or workspace wrapper")?;
    let args: Vec<_> = args.collect();
    let initial = Command::new(&compiler)
        .args(&args)
        .args(["-Zalways-encode-mir=yes", "-Zmir-opt-level=0"])
        .output()?;
    let produce = initial.status.success()
        && args
            .iter()
            .any(|arg| arg == "--emit" || arg.to_string_lossy().starts_with("--emit="))
        && args
            .iter()
            .any(|arg| arg == "--crate-name" || arg.to_string_lossy().starts_with("--crate-name="));
    if !produce {
        if initial.status.success() {
            std::io::stderr().write_all(&initial.stderr)?;
            std::io::stdout().write_all(&initial.stdout)?;
            return Ok(ExitCode::SUCCESS);
        }
        std::io::stderr().write_all(&without_artifact_notifications(&initial.stderr))?;
        std::io::stdout().write_all(&without_artifact_notifications(&initial.stdout))?;
        return Ok(ExitCode::FAILURE);
    }
    let driver = std::env::current_exe()?.with_file_name("miren");
    let mut producer = Command::new(driver);
    producer.arg("--produce-static-origins");
    if std::path::Path::new(&compiler)
        .file_stem()
        .is_some_and(|name| name == "rustc")
    {
        producer.arg(&compiler);
    }
    let evidence = producer
        .args(&args)
        .args(["-Zalways-encode-mir=yes", "-Zmir-opt-level=0"])
        .output()?;
    // Cargo pipelines consumers as soon as an artifact event arrives. Publish only the final
    // artifacts, after the producer has finished replacing metadata and writing its evidence.
    std::io::stderr().write_all(&without_artifact_notifications(&initial.stderr))?;
    std::io::stdout().write_all(&without_artifact_notifications(&initial.stdout))?;
    if !evidence.status.success() {
        std::io::stderr().write_all(&without_artifact_notifications(&evidence.stderr))?;
        std::io::stdout().write_all(&without_artifact_notifications(&evidence.stdout))?;
        return Ok(ExitCode::FAILURE);
    }
    std::io::stderr().write_all(&only_artifact_notifications(&evidence.stderr))?;
    std::io::stdout().write_all(&only_artifact_notifications(&evidence.stdout))?;
    Ok(ExitCode::SUCCESS)
}

fn main() -> ExitCode {
    match run() {
        Ok(status) => status,
        Err(error) => {
            eprintln!("miren-rustc: {error}");
            ExitCode::FAILURE
        }
    }
}

fn is_artifact_notification(line: &[u8]) -> bool {
    serde_json::from_slice::<serde_json::Value>(line)
        .ok()
        .is_some_and(|message| {
            message
                .get("$message_type")
                .and_then(serde_json::Value::as_str)
                == Some("artifact")
        })
}

fn without_artifact_notifications(output: &[u8]) -> Vec<u8> {
    output
        .split_inclusive(|byte| *byte == b'\n')
        .filter(|line| !is_artifact_notification(line))
        .flatten()
        .copied()
        .collect()
}

fn only_artifact_notifications(output: &[u8]) -> Vec<u8> {
    output
        .split_inclusive(|byte| *byte == b'\n')
        .filter(|line| is_artifact_notification(line))
        .flatten()
        .copied()
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{only_artifact_notifications, without_artifact_notifications};

    #[test]
    fn producer_failure_filters_only_json_artifact_notifications() {
        let artifact =
            b"{\"$message_type\":\"artifact\",\"artifact\":\"lib.rmeta\",\"emit\":\"metadata\"}\n";
        let diagnostic = b"{\"$message_type\":\"diagnostic\",\"message\":\"artifact failure\"}\n";
        let malformed = b"not json\n\xff";
        let input = [
            artifact.as_slice(),
            diagnostic.as_slice(),
            malformed.as_slice(),
        ]
        .concat();
        assert_eq!(only_artifact_notifications(&input), artifact);
        assert_eq!(
            without_artifact_notifications(&input),
            [diagnostic.as_slice(), malformed.as_slice()].concat()
        );
    }
}
