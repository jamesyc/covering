# Fresh replay: C(24,14,4) ≥ 20 and C(25,15,5) ≥ 34

Date: 2026-10-03. Machine: Apple Silicon Mac (arm64, 10 cores, 32 GB), James's laptop.
Performed by Claude Code at James's request. This is separate from the archived
campaign receipts, which came from the same pipeline that wrote the proof.

## Inputs
- Sources: `MAIN_PROOF/` from `covering_verified_lower_bounds_proof_essentials_20261003T1150Z.zip`,
  unmodified. The package's `verify_proof_package.py` passes; `FinalCoveringBounds.lean`
  SHA256 `559f5152…9e41` matches the archived value.
- Toolchain: Lean 4.34.1 (commit `5045d005`), installed with elan 4.2.4.
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. All 9 resolved dependency commits
  match the archived `lake-manifest.json`. Mathlib's own compiled files come from the
  official cache (`lake exe cache get`); Mathlib itself was not rebuilt.
- Build project: `lakefile.toml` declaring one library rooted at `MAIN_PROOF/`, listing
  the 80 modules in `SOURCE_ORDER.txt`.

## Commands
```
lake update && lake exe cache get
lake build                                   # 80/80 proof modules compiled from source
lake env lean IndependentCheck.lean          # independent textbook restatement
lake env leanchecker <module>                # for each of the 80 modules
```

## Results
- `lake build`: success. 0 errors, no `sorry`. Warnings are only deprecations and linter
  style hints. 1 min 19 s wall clock.
- 193 `#print axioms` reports. The union of all axioms is {propext, Classical.choice,
  Quot.sound}, Lean's standard three. All five final endpoints report exactly those.
- Source scan: no `sorry`/`admit`, no `axiom` declarations, no `native_decide`, no
  `implemented_by`/`extern`, no custom `elab`/`macro`/`syntax`, no `run_cmd`/`#eval`, no
  kernel-skipping or heartbeat options. The only `set_option` is `autoImplicit false`.
- `IndependentCheck.lean` restates both bounds with Mathlib `Finset`s, in the textbook
  form of a covering design: every k-subset family covering all t-subsets has at least N
  blocks. It derives them from the archived endpoints, using only the three standard
  axioms. So the archived `ValidBlock`/`IsCovering` hypotheses are implied by the
  textbook ones, and the archived theorem is at least as strong as the textbook statement.
- `leanchecker` (the kernel re-checker shipped with the toolchain) re-checked the
  declarations of all 80 modules through the kernel: 80/80 passed, 0 failures (760 s).
  The run was not `--fresh`, so Mathlib's declarations were not re-checked.

## Not covered by this replay
- Mathlib was taken from its official compiled cache, not rebuilt from source.
- `leanchecker --fresh`, a full from-scratch replay including Mathlib, was not run.
- No human has reviewed the Lean statement or the paper proof yet.

## Hashes
Recorded below.

```
lean: Lean (version 4.34.1, arm64-apple-darwin24.6.0, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)
lake-manifest sha256: 3cd81b013f0f8c68f0d76b2246bf8a81fdcae1fe729aea8b6985a6fc7f07b784
FinalCoveringBounds.lean sha256: 559f5152b8219e69cedc5cf2a9d9d5676b95288d6cf7bb21f84bf69163bb9e41
MAIN_PROOF tree sha256 (sorted file hashes): fb8d3ea7147fdda8f182882619b5519cb60be4c7ea24ab105be83f68764b31ac
IndependentCheck.lean sha256: 66b0e8e2053de8bf13684412133f9eec39e5b92c7d73c9c1e9bbc44f454e12e3
```
