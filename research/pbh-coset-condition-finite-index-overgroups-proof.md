---
rg: 2
id: pbh-coset-condition-finite-index-overgroups-proof
kind: route
title: The indicator of a finite set of cosets is an element of the lamplighter over G/C whose centralizer in G is the setwise stabilizer
target: pbh-coset-condition-passes-to-finite-index-overgroups
requires:
  - pbh-coset-wreaths-iff-identity-edge-hnns
---

**Item 1.** `C` is good, so by (a) of `pbh-coset-wreaths-iff-identity-edge-hnns`,
`L = Z/2 wr_(G/C) G = (⊕_(G/C) Z/2) ⋊ G` lies in `B_A`, and it contains `G`. Let
`m = 1_S ∈ ⊕_(G/C) Z/2` be the indicator function of the finite set `S`. In `L`,
`g m g^(-1) = 1_(gS)`. So `g` commutes with `m` iff `gS = S`. Hence
`C_G(m) = Stab_G(S)`, and condition (e) holds for `Stab_G(S)`, with this `L` and `m`.

**Item 2.** `C'` is a union of `[C' : C]` cosets of `C`, so `S = C'/C = {c'C : c' ∈ C'}`
is a finite subset of `G/C`. If `g ∈ C'`, then `gS = {gc'C} = S`. Conversely, if
`gS = S`, then `gC ∈ S` (take `c' = 1`), so `g ∈ C'`. So `Stab_G(S) = C'`, and item 1
applies.

**Normalizer example.** Take `C' = N_G(C)`.
