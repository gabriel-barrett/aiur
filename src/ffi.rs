//! A small C ABI transports versioned execution bytecode, never circuit data.
//! Lean's object ABI is confined to c/execution.c; Rust owns all execution state.
use crate::bytecode::Program;
use crate::hints::HintEntry;
use serde::Deserialize;
use serde_json::{Value as Json, json};
use std::ffi::{CString, c_char};

#[derive(Deserialize)]
struct Request {
    program: Program,
    entry: String,
    args: Option<Vec<Json>>,
    flat_args: Option<Vec<u64>>,
    #[serde(default)]
    hints: Vec<HintEntry>,
}
fn execute_request(bytes: &[u8]) -> Result<Json, String> {
    let request: Request =
        serde_json::from_slice(bytes).map_err(|e| format!("invalid execution request: {e}"))?;
    let program = request.program.check()?;
    let record = match (request.args, request.flat_args) {
        (Some(args), None) => {
            let entry = program.entry(&request.entry)?;
            if args.len() != entry.inputs.len() {
                return Err("entry argument count mismatch".into());
            }
            let values = entry
                .inputs
                .iter()
                .zip(&args)
                .map(|(t, v)| t.read_json(v))
                .collect::<Result<Vec<_>, _>>()?;
            program.execute_values_with_hints(&request.entry, &values, &request.hints)
        }
        (None, Some(args)) => program.execute_with_hints(&request.entry, args, &request.hints),
        _ => return Err("supply exactly one of args and flat_args".into()),
    }
    .map_err(|e| e.to_string())?;
    let entry = program.entry(&request.entry)?;
    let pretty_output = if entry.output.is_some() {
        Some(program.output_value(&request.entry, &record)?.to_string())
    } else {
        None
    };
    let mut queries = record.queries.iter().collect::<Vec<_>>();
    queries.sort_by_key(|(input, _)| *input);
    let queries = queries
        .into_iter()
        .map(|(input, output)| {
            json!({
                "function": input.function, "name": program.callable_name(input.function),
                "args": input.args, "output": output.output, "multiplicity": output.multiplicity,
                "hints": output.hints,
            })
        })
        .collect::<Vec<_>>();
    Ok(
        json!({ "output": record.output, "pretty_output": pretty_output, "queries": queries,
        "memory": record.memory, "instructions": record.instructions }),
    )
}

/// # Safety
/// `data` must address `length` readable bytes for the duration of this call.
/// The returned allocation must be released exactly once with `aiur_free_string`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn aiur_execute_json(data: *const u8, length: usize) -> *mut c_char {
    let response = std::panic::catch_unwind(|| {
        if data.is_null() {
            return Err("null execution request".into());
        }
        // SAFETY: the caller guarantees the buffer's validity; it is only borrowed.
        execute_request(unsafe { std::slice::from_raw_parts(data, length) })
    });
    let value = match response {
        Ok(Ok(value)) => json!({"ok": value}),
        Ok(Err(error)) => json!({"error": error}),
        Err(panic) => {
            let message = panic
                .downcast_ref::<String>()
                .map(String::as_str)
                .or_else(|| panic.downcast_ref::<&str>().copied())
                .unwrap_or("Rust execution panic");
            json!({"error": message})
        }
    };
    // JSON escapes all embedded NULs. No unwind may cross the C boundary.
    CString::new(value.to_string())
        .expect("JSON cannot contain a NUL byte")
        .into_raw()
}

/// # Safety
/// `string` must be null or a live pointer returned by `aiur_execute_json`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn aiur_free_string(string: *mut c_char) {
    if !string.is_null() {
        // SAFETY: ownership of precisely this CString allocation is returned.
        drop(unsafe { CString::from_raw(string) });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CStr;

    fn call(request: &Json) -> Json {
        let bytes = request.to_string().into_bytes();
        // SAFETY: the input buffer outlives the call. The returned string is
        // read before it is released once with the matching allocator.
        unsafe {
            let response = aiur_execute_json(bytes.as_ptr(), bytes.len());
            let json = serde_json::from_slice(CStr::from_ptr(response).to_bytes()).unwrap();
            aiur_free_string(response);
            json
        }
    }

    #[test]
    fn missing_hint_is_an_error_at_the_ffi_boundary() {
        let field = json!({"kind":"field"});
        let response = call(&json!({
            "program": {
                "version":1, "modulus":97, "enums":[], "maps":[], "tables":[],
                "functions":[{"name":"hinted", "params":[field], "result":field, "registers":2,
                    "code":[{"op":"hint", "type":field, "key_type":field, "key":[0], "dest":[1]},
                        {"op":"ret", "value":[1]}]}],
                "entries":[{"name":"main", "function":0, "inputs":[field], "output":field}]
            },
            "entry":"main", "args":[7]
        }));
        assert!(response["error"].as_str().unwrap().contains("missing hint"));
    }

    #[test]
    fn malformed_request_returns_owned_error_text() {
        let response = call(&json!({"entry":"missing"}));
        assert!(
            response["error"]
                .as_str()
                .unwrap()
                .contains("invalid execution request")
        );
    }
}
