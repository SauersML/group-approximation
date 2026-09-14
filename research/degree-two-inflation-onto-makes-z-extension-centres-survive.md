---
rg: 2
id: degree-two-inflation-onto-makes-z-extension-centres-survive
kind: claim
title: If every degree-two class with finite cyclic coefficients on a group is inflated from a finite quotient, the centre of every central Z-extension survives at every order in finite quotients
distinct_from:
  good-groups-have-no-persistent-finite-cohomology: that uses goodness to kill a finite-coefficient class on a finite-index subgroup; this uses the same inflation surjectivity to realise the reduction of an integral class in a finite quotient of the central extension, keeping its centre at full order
  z-extension-centre-orders-are-restricted-evaluation-indices: that computes the centre orders exactly as evaluation indices; this gives a sufficient profinite-cohomological condition under which they are unbounded
  hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class: that derives a failure of goodness from stability of a hyperlinear hyperbolic Kazhdan group; this derives visible central extensions, which destroy stability, from degree-two goodness, with no hyperlinearity assumption
---

**ESTABLISHED.** Let `K` be a group with the property

```text
(G2)  for every n >= 1, every class in H^2(K; Z/n) is the inflation of a class in H^2(K/N; Z/n)
      for some finite-index normal subgroup N of K.
```

Let `1 → Z = <z> → K~ → K → 1` be any central extension. Then for every `n >= 1` there is a
homomorphism from `K~` onto a finite group in which `z` has order exactly `n`.

**When (G2) holds.** If `K` is good in Serre's sense (for trivial coefficients `Z/n` in degree 2
suffices), then (G2) holds: continuous cohomology of `K^` with finite trivial coefficients is the
directed colimit over finite quotients, exactly as used in `good-no-persistent-cohomology-proof`.

**Consequence for Kazhdan groups.** Let `G` be a finitely generated Kazhdan group and `K <= G` a
finite-index subgroup with `b_2(K;Q) >= 1` satisfying (G2). By universal coefficients choose
`c ∈ H^2(K;Z)` with `c(H_2(K;Z)) != 0`; the extension `K~_c` has finite abelianization (as in the
Attempts of `ghb7-finite-index-z-extension-center-survives`), and its centre survives at every order.
For `G = G_{HB_2}(7)` this is route `ghb7-centre-survival-via-degree-two-goodness`.

DERIVATION
degree-two-inflation-surjectivity-centre-survival-proof
