---
rg: 2
id: raag-virtual-fn-kernel-implies-raag-fn-kernel
kind: claim
title: If a finite-index subgroup of a right-angled Artin group maps onto Z with kernel of type F_n, then so does the group itself
---

For every finite flag complex `L`, every `n ≥ 1`, and every subgroup `H ≤ A_L` of
finite index: if some epimorphism `ψ: H → Z` has kernel of type `F_n`, then some
epimorphism `χ: A_L → Z` has kernel of type `F_n`.

This is the affirmative answer to Zaremsky's Problem 1.19
(`zaremsky-1-19-raag-virtual-fn-kernel-conjecture`).

## Attempts

- 2026-09-13, lane z1-19-raag-kernel, later the same day: proved, UNREVIEWED, through the route
  `raag-virtual-fn-kernel-conjecture-via-sigma-invariants`. A kernel of type `F_n` gives
  `Σ^n(H) ≠ ∅`, and `raag-finite-index-sigma-m-forces-connected-flag-complex` makes `L`
  `(n−1)`-connected. The route does not fire until `bestvina-brady-kernel-finiteness-theorem` is
  imported with a verified citation.
- 2026-09-13, lane z1-19-raag-kernel, first plan: split into a homological part and a `π_1`
  part. The homological part (a kernel of type `FP_n(F)` on a finite-index subgroup
  forces `L` to be `(n−1)`-acyclic over `F`) is proved through Betti numbers over
  Malcev--Neumann division rings. What remains is to show that `L` must be simply
  connected when some finite-index subgroup has a finitely presented kernel. Given
  both parts, Hurewicz makes `L` `(n−1)`-connected, and Bestvina--Brady gives a kernel
  of type `F_n` for `A_L`.
