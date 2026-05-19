# Tama UniswapV2

Active spec guidance:

- `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean` and
  `verity/spec/TamaUniV2/Spec/UniswapV2FactorySpec.lean` are the single source
  of truth for what is covered and why. Read the top-of-file overview and
  section docstrings as the assurance argument; each `def pair_*` is the
  formal version of the paragraph above it.
- `docs/superpowers/plans/2026-05-17-invariant-first-uniswap-v2-specs.md` is the
  current forward plan.
- `docs/agent-progress.md` is append-only historical context; use it for
  checkpoints and failed-route lessons, not as the source of the current plan.

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
