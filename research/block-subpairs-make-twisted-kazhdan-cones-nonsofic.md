---
rg: 2
id: block-subpairs-make-twisted-kazhdan-cones-nonsofic
kind: claim
title: Block Kun-Thom subpairs make every nontrivially twisted Kazhdan cone over the Theorem E pair nonsofic in rank at least five
distinct_from:
  twisted-diagonal-cones-need-a-profinitely-invisible-core: that restricts the pair to finite-index normal levels and leaves the twists with a centreless invisible core, such as evaluation at the origin; this restricts it to infinite-index block subpairs, which kill every nontrivial twist in rank at least five, the invisible-core loophole included.
  kazhdan-double-cones-add-one-sigma1-bit: that proves the double embedding when an element centralises the whole amalgamated subgroup and names twisted-diagonal cones as the surviving route; this closes that route in rank at least five by embedding the double of a smaller Kun-Thom pair.
  finite-twisted-kazhdan-cone-is-sofic: that asks whether one explicit twisted cone is sofic; this answers no for rank at least five, and for rank four when q is not 2, 3 or 5.
  kt-pair-group-double-is-nonsofic: that is the literature input for a single pair; this applies it to the rank-three block pair sitting inside every larger-rank pair.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: [[block-subpairs-make-twisted-kazhdan-cones-nonsofic-proof]].
It answers [[finite-twisted-kazhdan-cone-is-sofic]] in the negative for `r ≥ 5`, and for `r = 4` when
`q ∉ {2, 3, 5}`.  It closes the twisted-cone route of [[kazhdan-double-cones-add-one-sigma1-bit]] to
[[sofic-recognition-finite-presentations-is-pi2-complete]] in those ranks.

## Setting

Take the Theorem E pair `Gamma = EL_r(R_+) ≤ G = EL_r(R) x| SL_d(Z)` of [[kun-thom-nonsofic-wreath]], with
`R_+ = F_q[x_1..x_d]`, `R = F_q[x_1^(±1)..x_d^(±1)]` and `r, d ≥ 3`.  For a group `H` and a homomorphism
`psi : Gamma -> H`, the **twisted-diagonal cone** is

```text
X(H, psi) = (H x Gamma) *_(Gamma_psi) G ,    Gamma_psi = { (psi(g), g) : g in Gamma } ≅ Gamma ≤ G .
```

For a 3-element set `S ⊆ {1..r}`, the **block subpair** is

```text
G_S = EL_S(R) x| SL_d(Z)  ≥  Gamma_S = EL_S(R_+) ,
```

where `EL_S` is the elementary group on the coordinates in `S`, acting as the identity on the others.

## Theorem

**(B1) Block subpairs are Kun-Thom pairs, and they are cut out by Gamma.**  `G_S` is a subgroup of `G`, and
`G_S ∩ Gamma = Gamma_S`.  The pair `Gamma_S ≤ G_S` is the Theorem E pair with parameters `(3, d)`, so the
double `G_S *_(Gamma_S) G_S` is nonsofic.  The intersection uses Suslin's theorem
`SL_n(F_q[x_1..x_d]) = EL_n(F_q[x_1..x_d])` for `n ≥ 3`.

**(B2) Subpair double embedding.**  Let `B ≤ G` be any subgroup and put `C = B ∩ Gamma`.  If some
`h ∈ H \ 1` centralises `psi(C)`, then `B *_C B` embeds in `X(H, psi)`, by `b ↦ b` on one copy and
`b ↦ h b h^-1` on the other.  With (B1): **if `C_H(psi(Gamma_S)) ≠ 1` for some `S`, then `X(H, psi)` is
nonsofic.**  A source of such `h` is `psi(C_Gamma(Gamma_S))`.

**(B3) Rank at least five: every twist dies.**  Let `r ≥ 5` and `H ≠ 1`.  Then `X(H, psi)` is nonsofic for
**every** homomorphism `psi : Gamma -> H`.
- If `psi` is trivial, any `h ∈ H \ 1` centralises `psi(Gamma)`; this is (K1) of
  [[kazhdan-double-cones-add-one-sigma1-bit]].
- If `psi` is nontrivial, some elementary matrix `e_ij(a)` has `psi(e_ij(a)) ≠ 1`, because these generate
  `Gamma`.  Pick `S` disjoint from `{i, j}`, which is possible since `r - 2 ≥ 3`.  Then `e_ij(a)` commutes with
  `Gamma_S`, so `psi(e_ij(a))` centralises `psi(Gamma_S)`, and (B2) applies.

No finiteness, amenability or visibility of the twist is used.

**(B4) Rank four.**  Let `r = 4` and `q ∉ {2, 3, 5}`, so some `a ∈ F_q^*` has `a^4 ≠ 1`.  Then `X(H, psi)` is
nonsofic for every `psi` and every `H ≠ 1`.  The element `D = diag(a, a, a, a^-3)` centralises
`Gamma_(123)`.  If `psi(D) = 1`, then `ker psi` contains `[D, e_14(t)] = e_14((a^4 - 1) t)` for every `t`, so
`ker psi ⊇ e_14(R_+)`.  Conjugating by monomial matrices of `SL_4(F_q) ≤ Gamma` gives every `e_ij(R_+)`, so
`psi` is trivial.  For `q ∈ {2, 3, 5}`, `C_Gamma(Gamma_S)` is the centre of `Gamma`, and (B2) only applies
when `C_H(psi(Gamma_S)) ≠ 1`.

**(B5) The finite twisted cone.**  Let `F = PSL_r(F_q)`, `psi = ev_0` followed by the projection, and let
`T = X(F, psi)` be the group of [[finite-twisted-kazhdan-cone-is-sofic]].
- `T` is **nonsofic** for `r ≥ 5` (every `q`), and for `r = 4` with `q ∉ {2, 3, 5}`.  An explicit
  centralising element for `S = {1,2,3}` is the image of `e_45(1)`, or of `diag(a, a, a, a^-3)` when `r = 4`.
- For `r = 4` with `q ∈ {2, 3, 5}`, `C_F(psi(Gamma_S)) = 1` for every `S`.  For `r = 3` the only block is
  `Gamma` itself.  So the block method says nothing there.

## Consequence for the route

The twisted-cone route asked for a sofic INF branch `X(H, psi)` with a Theorem E pair.  For `r ≥ 5`, and for
`r = 4` with `q ∉ {2,3,5}`, **no such branch exists for any `H ≠ 1` and any twist.**  The invisible-core
condition of [[twisted-diagonal-cones-need-a-profinitely-invisible-core]] is no longer the obstruction there,
since every cone is nonsofic.  The necessary condition for a sofic cone becomes much stronger than
`C_H(F_inf) = 1`:

```text
C_H( psi(B ∩ Gamma) ) = 1   for every subgroup B ≤ G whose double over B ∩ Gamma is nonsofic.
```

## What remains

The twisted-cone route survives only for the rank-three pairs, and for `r = 4` with `q ∈ {2, 3, 5}`.  For the
test group this is `T_3 = (PSL_3(F_q) x Gamma) *_(Gamma_(ev_0)) G` with `Gamma = EL_3(R_+)`, now the open node
[[rank-three-finite-twisted-kazhdan-cone-is-sofic]].  The block method
is empty there: it needs a 3-element block together with a disjoint centralising element, so it needs
`r ≥ 4`, and in rank four it needs a non-scalar diagonal centraliser.  The next step is one of two:

- find a Kazhdan subgroup `B ≤ G` of infinite index with `ev_0(B ∩ Gamma)` inside the centraliser of a
  nontrivial element of `PSL_3(F_q)` and with `B *_(B ∩ Gamma) B` nonsofic;
- or build sofic approximations of `T_3`.  By (V4) of the invisible-core node these cannot come from finite
  quotients.

A natural candidate for `B ∩ Gamma` is the finite-index kernel `Gamma(0) = ker ev_0`, which is Kazhdan,
infranormal and not normal in `G`.  But `G` itself is the subgroup generated by `Gamma(0)` and `SL_d(Z)`, so
`B` must avoid all but a few of the compressors.
