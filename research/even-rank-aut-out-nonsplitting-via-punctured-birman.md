---
rg: 2
id: even-rank-aut-out-nonsplitting-via-punctured-birman
kind: route
title: Restrict a virtual section in rank 2g to the once-punctured genus-g mapping class group and apply non-splitting there
target: aut-free-to-out-free-does-not-virtually-split-in-even-rank
requires:
  - free-group-virtual-sections-give-punctured-birman-sections
  - once-punctured-birman-sequence-does-not-virtually-split
artifacts:
  - research/artifacts/solve-bh-mcg-outfn-2026-09-13.md
---

Let `g ≥ 2`, and suppose `Aut(F_{2g}) → Out(F_{2g})` splits over a finite-index
`Γ`.

1. Take `k = 1`, so `2g + k − 1 = 2g`.
2. By `free-group-virtual-sections-give-punctured-birman-sections`, the Birman
   sequence `1 → π1(Σ_{g,1}) → PMod(Σ_{g,2}) → PMod(Σ_{g,1}) → 1` splits over the
   finite-index subgroup `Γ ∩ PMod(Σ_{g,1})`.
3. That contradicts `once-punctured-birman-sequence-does-not-virtually-split`.
