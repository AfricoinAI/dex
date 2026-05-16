# Tama UniswapV2

Run:

```sh
tama doctor
tama check
tama build
tama test
tama audit
```

## Continuous integration

`.github/workflows/ci.yml` runs `tama doctor --fix` for checkout-only generated
directories, verifies tracked dependency files did not change, then runs
`tama doctor`, `tama build --locked`, `tama test`, and `tama audit` on every push
and pull request. The first run installs Lean (elan), Foundry, Tama, and the solc
version configured in `tama.toml`; later runs reuse Lake package and Lean build
caches keyed on `lake-manifest.json`, `lakefile.toml`, `lean-toolchain`, and
`tama.lock`.
