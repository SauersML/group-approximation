---
rg: 2
id: brin-thompson-torsion-orders-escape-every-recursive-bound-proof
kind: route
title: Undecidable torsion problem plus the computability characterization
target: brin-thompson-torsion-orders-escape-every-recursive-bound
requires:
  - belk-bleak-2v-torsion-problem-is-undecidable
  - finiteness-decidable-iff-finite-subgroup-profile-recursive
---

1. **`2V` escapes.** By `belk-bleak-2v-torsion-problem-is-undecidable`, `2V` is
   finitely generated with solvable word problem and undecidable order problem.
   By item 1 of
   `finiteness-decidable-iff-finite-subgroup-profile-recursive`,
   `TO_(2V)` is not recursively bounded, for any finite generating set.
2. **Passing to `G`.** Let `K <= G` be a copy of `2V` with finite generating set
   `R`, and let `c` bound the `S`-lengths of `R`. By item 4 of the same node,
   `TO_(K,R)(L) <= TO_(G,S)(cL)`. If `TO_(G,S)` were recursively bounded by `U`,
   then `L -> U(cL)` would recursively bound `TO_(K,R)`, contradicting step 1.
3. **Infinitely often.** Suppose `TO_G(L) <= U(L)` for all `L >= L_0`, with `U`
   recursive. Then `max(U(L), TO_G(0), ..., TO_G(L_0))` is recursive, since it
   differs from `U` at finitely many places by fixed constants, and it bounds
   `TO_G` everywhere. This contradicts step 2. So `TO_G(L) > U(L)` infinitely
   often.
4. **`FS`.** A torsion element `g in B(L)` generates the finite subgroup `<g>`
   of order `ord(g)` from the subset `{g}` of `B(L)`, so `FS_G >= TO_G`. ∎
