---
rg: 2
id: fp-simple-amenable-via-labbe-shift-full-group
kind: route
title: An amenable finitely presented derived full group of Labbé's Wang shift would be the example
target: fp-infinite-simple-amenable-group
requires:
  - minimal-aperiodic-wang-shift-exists
  - minimal-z2-subshift-derived-full-groups-are-fg-simple
  - labbe-shift-derived-full-group-is-amenable
  - labbe-shift-derived-full-group-is-finitely-presented
artifacts:
  - research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md
---

## Why sufficient

1. **Infinite and simple.** `Omega_U` is an infinite minimal free `Z^2`-subshift (`minimal-aperiodic-wang-shift-exists`). So `D([[Z^2 ~ Omega_U]])` is infinite and simple (`minimal-z2-subshift-derived-full-groups-are-fg-simple`).
2. **The two open inputs.** If this group is also amenable and finitely presented (`labbe-shift-derived-full-group-is-amenable`, `labbe-shift-derived-full-group-is-finitely-presented`), it is an infinite, finitely presented, simple, amenable group. That is exactly the root.
3. **No false establishment.** Both inputs in step 2 are OPEN, so this route does not establish the root.
   - `labbe-shift-derived-full-group-escapes-known-obstructions` records that no obstruction on main refutes either input.
