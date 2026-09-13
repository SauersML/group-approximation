---
rg: 2
id: labbe-full-group-lef-via-periodic-relator-shifts
kind: route
title: DEAD - patch-rich periodic points of relator shifts would make Labbé's derived full group LEF
target: labbe-shift-derived-full-group-is-lef
requires: []
artifacts:
  - research/artifacts/labbe-lef-2026-09-12.md
  - research/artifacts/labbe-lef-crux-small-growth-models-2026-09-13.md
---

**Dead route (2026-09-13, ex2-labbe-lef-crux).** It is invalidated by
`labbe-relator-shift-periodic-points-carry-trivial-actions`, which is established (unreviewed). That claim
proves `n_0(S, R)` exists: for `n >= n_0`, every periodic point of every relator shift carries the trivial
action, whatever the extension and its radius. So its former premise
`labbe-relator-shifts-carry-patch-rich-periodic-points` is false, and this route cannot fire.

## Intended argument (kept for the record)

1. **Setting.**
   - `Omega_U` is a minimal `Z^2`-subshift with a free action (`minimal-aperiodic-wang-shift-exists`).
   - `Gamma = D([[Omega_U]])` is finitely generated (`minimal-z2-subshift-derived-full-groups-are-fg-simple`).
   - So the criterion `zd-subshift-full-group-lef-via-periodic-relator-shifts` applies to `Gamma` with any
     finite symmetric generating set.
2. **Hypotheses.** `labbe-relator-shifts-carry-patch-rich-periodic-points` would supply, for some generating set
   and every `n`, an extension and a periodic `y_n ∈ Z_n` satisfying (H1) and (H2).
3. **Conclusion.** The criterion would then give that `Gamma` is LEF.

## Why it dies

- The orbit of `y_n` is a finite `F(S)`-set that satisfies all relators of length `<= 2n`. Its Schreier balls
  grow at most like `9R^2 k^2`.
- By `labbe-full-group-finite-small-growth-models-are-trivial`, such a model carries the trivial action for
  `n >= n_0`.
- (H1) and (H2) force some generator to move a point.
