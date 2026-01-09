# template-rust-lib

Base template for a Rust library with CI and config files

## Usage

- Run the following to remove template language:
```
# Replace all occurrences with the desired library name
$ rg -i template --glob '!deny.toml'
# Update Rust toolchain if desired in `rust-toolchain.toml` and `Cargo.toml`
# Then rewrite this `README`
```
- Edit licenses and `deny.toml` as needed

## License

MIT or Apache 2.0
