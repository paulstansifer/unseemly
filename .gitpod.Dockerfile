FROM gitpod/workspace-full

# For nightly rustfmt:
RUN bash -cl "rustup toolchain install nightly --allow-downgrade -c rustfmt"
# For the Web IDE:
RUN bash -cl "cargo install wasm-pack"