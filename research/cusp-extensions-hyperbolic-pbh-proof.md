---
rg: 2
id: cusp-extensions-hyperbolic-pbh-proof
kind: route
title: The maximal elementary subgroup of h is its centralizer, so the cusp extension is a centralizer amalgam; Dahmani gives the relative hyperbolicity
target: cusp-extensions-of-torsion-free-hyperbolic-groups-satisfy-pbh
requires:
  - pbh-class-closed-under-centralizer-amalgams
  - hyperbolic-groups-lie-in-the-permutational-class
  - hyperbolic-group-relative-to-maximal-elementary-subgroup
  - rel-hyperbolic-fp-simple-peripherals-proof
---

**E(h) = C_H(h), infinite cyclic.** Standard facts, not re-read: a torsion-free virtually
cyclic group is infinite cyclic; and for `h` of infinite order in a hyperbolic group,
`E(h) = {g : g h^n g^{-1} = h^{±n} for some n ≠ 0}` (Olshanskii 1993, Lemma 1.16).
`h` has infinite order (torsion-free), and `E(h)` is elementary and contains `h`
(`hyperbolic-group-relative-to-maximal-elementary-subgroup`, item 1), so `E(h)` is
infinite cyclic. Being abelian and containing `h`, it lies in `C_H(h)`. Conversely
`g h g^{-1} = h` puts `g` in `E(h)` by the displayed formula with `n = 1`.

**Item 1.** `H` is finitely generated and in `B_A`
(`hyperbolic-groups-lie-in-the-permutational-class`). Apply
`pbh-class-closed-under-centralizer-amalgams` with `M = H`, `F = {h}`:
`H *_{C_H(h)} (C_H(h) × P) = Γ ∈ B_A`.

**Item 2.** `H` is hyperbolic relative to `{E(h)}`
(`hyperbolic-group-relative-to-maximal-elementary-subgroup`, item 3; the trivial
subgroup in that family can be dropped). `E(h) × P` is finitely generated and
contains `E(h)`. Dahmani's combination theorem, Theorem 0.1(2), as quoted in
`rel-hyperbolic-fp-simple-peripherals-proof`, gives that `Γ` is hyperbolic
relative to the conjugates of `E(h) × P`. That route's trust note on the agreement
of Osin's and Bowditch's definitions applies here too. `E(h) × P ∈ B_A` by closure
under finite direct products (`Z ≤ V`, as in `pbh-centralizer-amalgam-closure-proof`).
