fn main() {
    println!("cargo:rerun-if-env-changed=IX_BENCH_NATIVE");
    let source = std::env::var("IX_BENCH_NATIVE")
        .expect("set IX_BENCH_NATIVE to ExportBenchmark.lean's generated .rs file");
    let source = std::fs::canonicalize(source).unwrap();
    let bytecode = source.with_extension("json");
    println!("cargo:rerun-if-changed={}", source.display());
    println!("cargo:rerun-if-changed={}", bytecode.display());
    let out = std::path::PathBuf::from(std::env::var_os("OUT_DIR").unwrap());
    std::fs::write(
        out.join("native_module.rs"),
        format!(
            "#[path = {source:?}] mod native;\nconst BYTECODE: &str = include_str!({bytecode:?});"
        ),
    )
    .unwrap();
}
