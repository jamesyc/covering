# Complete scientific source closure for the final covering bounds

This directory contains all80 scientific Lean source modules transitively
imported by `FinalCoveringBounds`, preserving their exact module paths. Sources
are copied byte-for-byte from the author-checked, hash-bound dependency graph.
The final combined independent acceptance receipt is stored in the campaign's
reviewer directory; consult that receipt for the latest final status.

Final public endpoints in namespace `Covering.FinalCoveringBounds`:

- `c24_14_4_lower_twenty`: for any `T : Covering.Family 24`, actual row validity
  `forall R in T, ValidBlock 14 R` and actual `IsCovering 4 T` imply
  `20 <= T.length`.
- `c25_15_5_lower_thirty_four`: for any `F : Covering.Family 25`, actual row
  validity `forall R in F, ValidBlock 15 R` and actual `IsCovering 5 F` imply
  `34 <= F.length`.
- `no_design24_at_most_nineteen` and `no_design25_at_most_thirty_three` are the
  corresponding canonical-Design nonexistence statements.

Repeated row slots are permitted in the universal lower-bound endpoints.
There are no rank, component, twin, gadget, omitted-set, or exact19-contradiction
premises in those endpoints. No matching construction or upper bound is claimed.

## Restore

1. Use Lean4.34.1 and official Mathlib v4.34.1 at commit
   d13f23b723b8a846827a245b89c10fc7d3f11612. Keep its official dependency manifest.
   Restore the matching official Mathlib compiled cache rather than rebuilding
   all of Mathlib. No new dependency is required.
2. Verify every file against `SOURCE_MANIFEST.json`. Its origins are provenance,
   not required paths: the local `path` keys and this tree are self-contained.
3. Set LEAN_PATH to this source directory followed by the pinned official
   Mathlib/dependency compiled-library paths. No other scientific `.olean`
   directory is necessary when replaying this complete source closure.
4. Compile the modules in `SOURCE_ORDER.txt` using the direct pinned `lean -j 1`,
   generating each module's local `.olean` beside its source. Preserve the
   directory hierarchy. Do not retain a Lake build parent.
5. Check `FinalCoveringBounds.lean` and its five `#print axioms` outputs. Each
   endpoint uses only `propext`, `Classical.choice`, and `Quot.sound`.
6. Replay the explicit exact-input, missing-premise, sharp/repeated-slot and
   custom-axiom controls from the frozen stage packets and independent reviewer
   receipts when reproducing the full audit rather than just the theorem chain.

This README describes restoration, not permission to launch an unbounded build.
Use the campaign's bounded single-heavy-process runner limits and secure a total
CPU allocation for a full80-module scientific replay. Vendor/cache trees are
intentionally not copied into this recovery closure.

`SOURCE_MANIFEST.json` records module import edges, topological source order,
exact SHA256 hashes, byte sizes, provenance paths and the18 external imports.
No source edits, vendored Mathlib code, generated proof axioms or stale compiled
objects were introduced when collecting this tree.
