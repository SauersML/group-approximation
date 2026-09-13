---
rg: 2
id: labbe-full-group-lef-via-periodic-relator-shifts
kind: route
title: Patch-rich periodic points of relator shifts would make Labbé's derived full group LEF
target: labbe-shift-derived-full-group-is-lef
requires:
  - minimal-aperiodic-wang-shift-exists
  - minimal-z2-subshift-derived-full-groups-are-fg-simple
  - zd-subshift-full-group-lef-via-periodic-relator-shifts
  - labbe-relator-shifts-carry-patch-rich-periodic-points
artifacts:
  - research/artifacts/labbe-lef-2026-09-12.md
---

## Why sufficient

1. **Setting.**
   - `Omega_U` is a minimal `Z^2`-subshift with a free action (`minimal-aperiodic-wang-shift-exists`).
   - `Gamma = D([[Omega_U]])` is finitely generated (`minimal-z2-subshift-derived-full-groups-are-fg-simple`).
   - So the criterion `zd-subshift-full-group-lef-via-periodic-relator-shifts` applies to `Gamma` with any finite symmetric generating set.
2. **Hypotheses.** `labbe-relator-shifts-carry-patch-rich-periodic-points` supplies, for some generating set and every `n`, an extension and a periodic `y_n ∈ Z_n` satisfying (H1) and (H2).
3. **Conclusion.** The criterion gives that `Gamma` is LEF.
4. **No false establishment.** The input in step 2 is OPEN, so this route does not establish its target.
