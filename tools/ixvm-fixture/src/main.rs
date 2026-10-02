use ix_common::{address::Address, env::ReducibilityHints};
use serde_json::json;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 4 {
        return Err("usage: ixvm-fixture ENV.ixe LEAN.NAME OUTPUT.json".into());
    }
    let data = std::fs::read(&args[1])?;
    let env = ixon::Env::get(&mut data.as_slice())?;
    let target = env
        .named
        .iter()
        .find(|e| e.key().to_string() == args[2])
        .ok_or("target not found")?
        .value()
        .addr
        .clone();
    let mut constants: Vec<_> = env
        .consts
        .iter()
        .map(|e| {
            let bytes = e.value().raw_bytes();
            assert_eq!(&Address::hash(bytes), e.key());
            let hint = env
                .anon_hints
                .get(e.key())
                .map(|h| match *h {
                    ReducibilityHints::Opaque => 0u64,
                    ReducibilityHints::Abbrev => 0xffff_ffff,
                    ReducibilityHints::Regular(n) => (u64::from(n) + 1).min(0xffff_fffe),
                })
                .unwrap_or(0);
            (
                e.key().hex(),
                json!({"address": e.key().as_bytes(), "bytes": bytes, "hint": hint}),
            )
        })
        .collect();
    constants.sort_by(|a, b| a.0.cmp(&b.0));
    let mut blobs: Vec<_> = env
        .blobs
        .iter()
        .map(|e| {
            assert_eq!(&Address::hash(e.value()), e.key());
            (
                e.key().hex(),
                json!({"address": e.key().as_bytes(), "bytes": e.value(), "hint": 0}),
            )
        })
        .collect();
    blobs.sort_by(|a, b| a.0.cmp(&b.0));
    // A correctly hashed but ill-typed theorem distinguishes proof checking
    // from merely verifying the serialization's content address.
    let mut invalid = env
        .get_const(&target)
        .ok_or("missing target bytes")?
        .as_ref()
        .clone();
    let ixon::ConstantInfo::Defn(definition) = &mut invalid.info else {
        return Err("negative fixture requires a standalone definition".into());
    };
    definition.value = definition.typ.clone();
    let mut invalid_bytes = Vec::new();
    invalid.put(&mut invalid_bytes);
    let invalid_address = Address::hash(&invalid_bytes);
    let fixture = json!({
        "format": "ixon-v3", "name": args[2], "address": target.as_bytes(),
        "addressHex": target.hex(),
        "invalidProof": {"address": invalid_address.as_bytes(), "bytes": invalid_bytes, "hint": 0},
        "constants": constants.into_iter().map(|(_,v)| v).collect::<Vec<_>>(),
        "blobs": blobs.into_iter().map(|(_,v)| v).collect::<Vec<_>>()
    });
    std::fs::write(&args[3], serde_json::to_string(&fixture)? + "\n")?;
    eprintln!(
        "{}: {} ({} constants, {} blobs)",
        args[2],
        target.hex(),
        env.consts.len(),
        env.blobs.len()
    );
    Ok(())
}
