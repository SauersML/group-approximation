---
rg: 2
id: twisted-diagonal-cones-need-a-profinitely-invisible-core-proof
kind: route
title: Restrict the Kun-Thom pair to a finite-index level, embed its double through the centraliser of the level, and compute the levels of evaluation at the origin
target: twisted-diagonal-cones-need-a-profinitely-invisible-core
requires:
  - kt-pair-group-double-is-nonsofic
---

Notation is as in [[twisted-diagonal-cones-need-a-profinitely-invisible-core]].  Write `S = P_Gamma =
{ t ∈ G : t Gamma t^-1 ≤ Gamma }`.  It is a monoid, it contains `Gamma`, and it generates `G`.

Facts used:
- (F1) Normal form in amalgams (Serre, *Trees*, I.1.2).
- (F2) Subgroups and finite-index overgroups of sofic groups are sofic.  Finite-index subgroups of Kazhdan
  groups are Kazhdan.
- (F3) Kun-Thom Theorem A (v3), as recorded in [[kt-pair-group-double-is-nonsofic]]: for a Kun-Thom pair,
  `G *_Gamma G` is nonsofic.
- (F4) The double embedding (K1) of [[kazhdan-double-cones-add-one-sigma1-bit]]: if `C ≤ A` and `y ∈ A \ C`
  centralises `C`, then `B *_C B` embeds in `A *_C B`, by `b ↦ b` on one copy and `b ↦ y b y^-1` on the other.

## (V1) Levels restrict Kun-Thom pairs

Let `G_1 ⊴ G` have finite index, let `pi : G -> Q = G/G_1`, and put `Gamma_1 = Gamma ∩ G_1`.

*Step 1: `pi(S) = Q`.*  `pi(S)` is a submonoid of the finite group `Q`, hence a subgroup, and it generates
`pi(G) = Q`.  For each `s ∈ S` fix `s' ∈ S` with `pi(s') = pi(s)^-1`.

*Step 2: `W = <S ∩ G_1>` is normal in `G`.*  Let `s ∈ S` and `w ∈ S ∩ G_1`.  Then `s w s'` and `s s'` lie in
`S ∩ G_1`, so `s w s^-1 = (s w s')(s s')^-1 ∈ W`.  Hence `s W s^-1 ⊆ W`.  Also `s^-1 = s' (s s')^-1` with
`s s' ∈ W`, so `s^-1 W s = s' W s'^-1 ⊆ W`.  Since `S` generates `G`, `W ⊴ G`.

*Step 3: `W = G_1`.*  If `s, t ∈ S` have `pi(s) = pi(t)`, then `s t'` and `t t'` lie in `W`.  So `s` and `t`
both have image `t'^-1` in `G/W`.  The image of `S` in `G/W` therefore has at most `|Q|` elements.  It is a
finite submonoid of a group, hence a subgroup, and it generates `G/W`.  So `|G/W| ≤ |Q| = |G/G_1|`, and
`W ≤ G_1` gives `W = G_1`.

*Step 4: `Gamma_1` is infranormal in `G_1`.*  For `t ∈ S ∩ G_1`,
`t Gamma_1 t^-1 ≤ t Gamma t^-1 ∩ G_1 ≤ Gamma ∩ G_1 = Gamma_1`, using that `G_1` is normal.  So the compression
semigroup of `Gamma_1` in `G_1` contains `S ∩ G_1`, which generates `G_1` by Step 3.

*Step 5: `Gamma_1` is not normal in `G_1`.*  If every `s ∈ S` normalised `Gamma`, then `G = <S>` would
normalise it.  So some `c ∈ S` has `c Gamma c^-1 < Gamma` strictly.  Let `n` be the order of `pi(c)` and
`d = c^n ∈ S ∩ G_1`.  Then `d Gamma d^-1 ≤ c Gamma c^-1 < Gamma`.  Suppose `Gamma_1 ⊴ G_1`.  Then
`d Gamma_1 d^-1 = Gamma_1`, so `Gamma_1 ≤ d Gamma d^-1 < Gamma`.  Now `[Gamma : Gamma_1]` is finite and

```text
[Gamma : Gamma_1] = [Gamma : d Gamma d^-1] · [d Gamma d^-1 : d Gamma_1 d^-1] = [Gamma : d Gamma d^-1] · [Gamma : Gamma_1],
```

so `[Gamma : d Gamma d^-1] = 1`, a contradiction.

*Step 6.*  `G_1` and `Gamma_1` have finite index in `G` and `Gamma`, so they are Kazhdan by (F2).  So
`Gamma_1 ≤ G_1` is a Kun-Thom pair, and `G_1 *_(Gamma_1) G_1` is nonsofic by (F3).  ∎

## (V2) Virtual double embedding

Let `z ∈ C_H(psi(Gamma_1))` with `z ≠ 1`.  Put `Z = C_H(psi(Gamma_1))` and

```text
A = { (u psi(g), g) : u ∈ Z, g ∈ Gamma_1 }  ≤  H x Gamma .
```

- *`A` is a subgroup.*  `(u_1 psi(g_1), g_1)(u_2 psi(g_2), g_2) = (u_1 u_2 psi(g_1 g_2), g_1 g_2)`, since `u_2`
  commutes with `psi(g_1)`.  Inverses are similar.
- *`A ∩ Gamma_psi = (Gamma_1)_psi`.*  `(u psi(g), g) ∈ Gamma_psi` forces `u psi(g) = psi(g)`, so `u = 1`.
- *`B = G_1` has `B ∩ Gamma = Gamma_1`.*  Under the identification this is the same subgroup
  `C = (Gamma_1)_psi`.

By (F1), `<A, B> = A *_C B` inside `X(H, psi)`.  A reduced word alternates `A \ C ⊆ (H x Gamma) \ Gamma_psi` and
`B \ C ⊆ G \ Gamma`, so it is reduced in `X` and nontrivial.

The element `y = (z, 1) ∈ A` is not in `C`, because `z ≠ 1`.  It centralises `C`:
`(z,1)(psi(g), g)(z^-1, 1) = (z psi(g) z^-1, g) = (psi(g), g)` for `g ∈ Gamma_1`.  By (F4),
`G_1 *_(Gamma_1) G_1` embeds in `A *_C G_1 ≤ X(H, psi)`.  By (V1) and (F2), `X(H, psi)` is nonsofic.  ∎

## (V3) The invisible core

A Kazhdan group has only finite amenable quotients, so `F = psi(Gamma)` is finite when `H` is amenable.  If
`G_1 ⊆ G_2` are levels, then `psi(Gamma ∩ G_1) ⊆ psi(Gamma ∩ G_2)`.  Levels are closed under finite
intersections, so the family `psi(Gamma ∩ G_1)` is downward directed in the finite set of subgroups of `F`.
It has a least element, attained at some level.  That element is `F_inf`.  It is normal in `F`, since
`Gamma ∩ G_1 ⊴ Gamma`.

- If `C_H(F_inf) ≠ 1`, apply (V2) at a level attaining `F_inf`.
- If `F_inf = 1`, then `C_H(F_inf) = H ≠ 1`.
- If `Z(F_inf) ≠ 1`, then `C_H(F_inf) ⊇ Z(F_inf) ≠ 1`.
- *Subgroup.*  `F x Gamma ≤ H x Gamma` contains `Gamma_psi`.  So by (F1), `<F x Gamma, G> = (F x Gamma)
  *_(Gamma_psi) G = X(F, psi)`, and this is a subgroup of `X(H, psi)`.  ∎

## (V4) The finite residual

Let `rho : X(H, psi) -> Q'` be a homomorphism onto a finite group.  Then `ker(rho|G)` contains a level `G_2`,
and `psi(Gamma ∩ G_2) ⊇ F_inf`.  For `g ∈ Gamma ∩ G_2` we have `rho(psi(g), g) = 1`.  So
`rho(psi(g), 1) = rho(1, g)^-1`.  Hence `rho(psi(Gamma ∩ G_2) x 1) ≤ rho(1 x Gamma)`, which commutes with
`rho(H x 1) ⊇ rho(psi(Gamma ∩ G_2) x 1)`.  So `rho(psi(Gamma ∩ G_2) x 1)` is abelian, and `rho` kills
`[F_inf, F_inf] x 1`.  This subgroup is nontrivial in `X` when `F_inf` is nonabelian, because `H x Gamma`
embeds in `X`.  ∎

## (V5) Evaluation at the origin

Let `R = F_q[x_1^(±1), ..., x_d^(±1)]`, `R_+ = F_q[x_1, ..., x_d]`, `r ≥ 3`, and let `L ⊴ G` be a level.  For
`i ≠ j` put `A_ij = { a ∈ R : e_ij(a) ∈ L }`.  It is an additive subgroup of finite index, being the preimage of
`L` under the homomorphism `a ↦ e_ij(a) L` into `G/L`.

Fix `k ∉ {i, j}`.  For `a ∈ A_ik` and `b ∈ R`, `e_ij(ab) = [e_ik(a), e_kj(b)] ∈ L`, since `L` is normal.  So
the ideal `J = A_ik R` lies in `A_ij`.  It has finite index, because it contains `A_ik`.  The ring `R/J` is
finite, and `x_1` is a unit in it, so `x_1^n ≡ 1 (mod J)` for some `n ≥ 1`.  Hence `a(x_1^n - 1) ∈ J ⊆ A_ij`
for all `a ∈ F_q`.  So `e_ij(a(x_1^n - 1)) ∈ Gamma ∩ L`, and `ev_0` of it is `e_ij(-a)`.

Taking `n` common to all pairs `(i, j)`, we get `ev_0(Gamma ∩ L) ⊇ { e_ij(a) } `, which generates
`SL_r(F_q)`.  So `F_inf(ev_0) = SL_r(F_q)`.  After projecting to `PSL_r(F_q)` (simple, since `r ≥ 3`), the core
is `F = PSL_r(F_q)`, and `C_F(F) = 1`.  ∎

## Calibration

- *Untwisted case.*  `psi = 1` has `F_inf = 1`, and (V2) at `G_1 = G` is (K1) applied to `Y = H x Gamma`.
  Here `Gamma_psi = 1 x Gamma`, so `X(H, 1)` is the Kazhdan cone `X(H, C)` with `C = H`, and (V2) recovers its
  nonsofic branch.
- *No false soficity claim.*  Every conclusion here is nonsoficity, obtained by embedding a Kun-Thom double.
  (V4) is the only structural statement about the positive side, and it only says which certificates cannot
  work.
