# Verification records

These replays rebuilt and re-checked the agents' original proof on 3 October 2026, before it
was registered as Palomar version 1. That proof lived in `MAIN_PROOF/`, which the files below
refer to; it is kept at the tag [`agent-proof-v1`](../../../tree/agent-proof-v1).

- [`REPLAY_2026-10-03_lean-4.34.1.md`](REPLAY_2026-10-03_lean-4.34.1.md): the sources as the
  agents left them, on Lean 4.34.1.
- [`REPLAY_2026-10-03_lean-4.35.0-rc3.md`](REPLAY_2026-10-03_lean-4.35.0-rc3.md): after the
  port to Lean 4.35.0-rc3 and the module system.

The current proof, in [`Covering/`](../Covering/), is built and checked with Comparator by CI
on every push, and was checked again by Palomar for version 2.
