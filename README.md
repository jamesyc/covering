# Lower bounds for the covering numbers C(24,14,4) and C(25,15,5)

A *(v, k, t) covering design* is a family of k-element subsets (blocks) of a v-element set
such that every t-element subset lies in at least one block. The covering number
C(v, k, t) is the smallest possible number of blocks.

This repository contains a Lean 4 proof of two new lower bounds:

| | Previous lower bound | New lower bound | Best known covering |
|---|---|---|---|
| C(24,14,4) | 19 | **20** | 23 |
| C(25,15,5) | 32 | **34** | 42 |

The previous values are from the [La Jolla Covering Repository](https://dmgordon.org/covering-designs/)
and [coveringrepository.com](https://coveringrepository.com/). The second bound follows from the
first by the Schönheim bound: ⌈25 · 20 / 15⌉ = 34. Applying it further also gives
C(26,16,6) ≥ 56, C(27,17,7) ≥ 89 and C(28,18,8) ≥ 139, which are not formalized here.

## Status

AI agents wrote the proof, in an OpenAI Dots multi-agent workspace over about three days. It
builds with Lean 4.35.0-rc3 and Mathlib `v4.35.0-rc3`, and uses only Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). **No mathematician has reviewed it yet.** If you
find a problem with the proof or the statement, please open an issue.

## The statement

[`Challenge.lean`](Challenge.lean) is the part to audit. It uses only Mathlib's `Finset` and
the standard definition of a covering design:

```lean
theorem Covering.Palomar.covering_24_14_4_lower_bound (𝒯 : Finset (Finset (Fin 24)))
    (hk : ∀ B ∈ 𝒯, B.card = 14)
    (hcov : ∀ S : Finset (Fin 24), S.card = 4 → ∃ B ∈ 𝒯, S ⊆ B) :
    20 ≤ 𝒯.card

theorem Covering.Palomar.covering_25_15_5_lower_bound (𝒯 : Finset (Finset (Fin 25)))
    (hk : ∀ B ∈ 𝒯, B.card = 15)
    (hcov : ∀ S : Finset (Fin 25), S.card = 5 → ∃ B ∈ 𝒯, S ⊆ B) :
    34 ≤ 𝒯.card
```

[`Solution.lean`](Solution.lean) proves exactly these declarations, and
[Comparator](https://github.com/leanprover/comparator) checks that the two match
([`comparator.json`](comparator.json)).

The proof itself works with a list-based model in
[`MAIN_PROOF/Statements/Model.lean`](MAIN_PROOF/Statements/Model.lean), which allows repeated
blocks. Its final theorems are in [`MAIN_PROOF/FinalCoveringBounds.lean`](MAIN_PROOF/FinalCoveringBounds.lean).
[`IndependentCheck.lean`](IndependentCheck.lean) derives the `Finset` statements from them.

## Checking it yourself

Install [elan](https://github.com/leanprover/elan), then run:

```bash
lake exe cache get
```

```bash
lake build
```

The first command downloads Mathlib's compiled files. The second compiles the proof and prints
the axioms each final theorem uses; it takes a few minutes on a laptop.
`lake env leanchecker <Module>` re-checks a module's declarations with Lean's kernel.
[`scripts/verify-comparator.sh`](scripts/verify-comparator.sh) runs Comparator the way Palomar
does; it needs Linux with `bwrap`, and CI runs it on every push.

## Layout

- `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`: the
  [Palomar](https://palomar-registry.org/) submission surface. Submissions go through
  <https://submit.palomar-registry.org/>.
- `MAIN_PROOF/`: the 80 Lean modules of the proof, in the layout the agents produced. Names such
  as `A19…`, `Physical…`, `rounds/` and `campaigns/` come from that process; renaming them to
  standard terminology is planned. `SOURCE_ORDER.txt` lists the modules in dependency order, and
  `SOURCE_MANIFEST.json` records their original hashes and import edges.
- `IndependentCheck.lean`: the `Finset` restatement.
- `verification/`: records of fresh builds and kernel re-checks.

## History

The tag [`original-2026-10-03`](../../tree/original-2026-10-03) holds the sources exactly as the
agents produced them, pinned to Lean 4.34.1 and Mathlib `d13f23b7`. Since then the project has
moved to Lean 4.35.0-rc3 (no source changes) and to Lean's module system. The module port adds
module headers and `public import`s to every file; no proof changed.

## License

Apache-2.0. See [LICENSE](LICENSE).
