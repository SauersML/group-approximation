---
rg: 2
id: level-subpair-line-sections-are-bounded-or-cofinite
kind: claim
title: For a level subpair of the rank-three cone, the section of the elementary part along a monomial Laurent line either has t-pole order at most 2 ceil(k/|m|) or has finite index in SL_3(F_q[t^(±1)]), and in the second case the subpair is not a certificate; so thin line sections do not exist
distinct_from:
  normalised-level-subpairs-cannot-certify-rank-three-cone: that kills E_B when it virtually contains, or is normalised by, an elementary group with a monomial unit, and leaves thin line sections open; this proves an intermediate-subgroup dichotomy for the sections along monomial lines, so a thin section cannot occur, and a single element with a deep pole on a line already puts E_B in the case killed there.
  rank-three-finite-twisted-kazhdan-cone-is-sofic: that is the open question; this narrows its level-containing nonsofic side to elementary parts that are pole-bounded on every monomial line.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: [[level-subpair-line-sections-are-bounded-or-cofinite-proof]].
It is an obstruction on the nonsofic side of [[rank-three-finite-twisted-kazhdan-cone-is-sofic]].  It settles
the thin-section case left open by [[normalised-level-subpairs-cannot-certify-rank-three-cone]]: that case
is empty.

## Setting

As in [[normalised-level-subpairs-cannot-certify-rank-three-cone]]: `R_+ = F_q[x_1..x_d]`, `R` the Laurent ring,
`Gamma = SL_3(R_+)`, `G = EL_3(R) x| SL_d(Z)`, `psi = ev_0`, and
`U_k = < e_ab(x^m) : a ≠ b, m ∈ N^d, |m| ≥ k >`.  For `B ≤ G`, `C = B ∩ Gamma` and `E_B = B ∩ EL_3(R)`.

For `m ∈ N^d \ {0}` put `t = x^m`, `A_m = F_q[t, t^-1] ⊆ R` and `n = ⌈k / |m|⌉`.  The **line section** of `E_B`
along `m` is `Δ_m = E_B ∩ SL_3(A_m)`.  The **pole order** of `g ∈ SL_3(A_m)` at `t = 0` is the largest `j ≥ 0`
such that some entry of `g` has a nonzero coefficient of `t^(-j)`.

## Theorem

**(L1) One-variable intermediate-subgroup dichotomy.**  Let `Γ_0` be a subgroup of finite index in
`SL_3(F_q[t])` that contains `e_ab(t^n F_q[t])` for all `a ≠ b`.  Let `Γ_0 ≤ Δ ≤ SL_3(F_q[t, t^-1])`.  Then
exactly one of the following holds.

1. `Δ` has finite index in `SL_3(F_q[t, t^-1])`.
2. `Δ` stabilises a lattice `L` with `t^(2n) L_0 ⊆ L ⊆ L_0`, `L_0 = F_q[[t]]^3`.  Then every element of `Δ` has
   pole order at most `2n` at `t = 0`, and `Δ` is commensurable with `SL_3(F_q[t])`.

So one element of `Δ` with pole order greater than `2n` forces case 1.  No subgroup of `SL_3(F_q[t, t^-1])`
containing `Γ_0` is both unbounded at `t = 0` and of infinite index.

**(L2) Line sections of level subpairs.**  Let `B ⊇ U_k` and `m ∈ N^d \ {0}`.  Then `Δ_m ⊇ E_3(t^n F_q[t])`, and
(L1) applies to `Δ_m`.

- If some element of `Δ_m` has pole order `> 2n` at `t = 0`, then `e_ab(1) ∈ E_B` for all `a ≠ b`.  So
  `C ⊇ SL_3(F_p)`, `C_F(psi(C)) = 1`, and `B` is not a Kun-Thom certificate for `T_3`.
- Otherwise `Δ_m` lies in a vertex stabiliser at `t = 0` and is commensurable with `SL_3(F_q[t])`.

**(L3) No thin sections.**  The group `Δ_l = E_B ∩ SL_3(F_q[s^(±1)])`, `s = x_l^c`, of
[[normalised-level-subpairs-cannot-certify-rank-three-cone]] is never thin.  If it has infinite index in
`SL_3(F_q[s^(±1)])`, it is commensurable with `SL_3(F_q[s])`, and its elements have pole order at most
`2 ⌈k/c⌉` at `s = 0`.

## Mechanism

1. Put `G_0 = SL_3(F_q((t)))` and `K = SL_3(F_q[[t]])`.  The closure of `Γ_0` in `G_0` has finite index in the
   closure `K` of `SL_3(F_q[t])`, so it is open.  Hence the closure of `Δ` is open.
2. *Unbounded.*  An open, non-compact subgroup of `G_0` is `G_0`, by Howe-Moore (or Tits-Prasad).  So `Δ` is
   dense.  With `K_1 = closure(Γ_0)`, density gives `SL_3(F_q[t^(±1)]) = Δ · (SL_3(F_q[t^(±1)]) ∩ K_1)`.  The
   second factor lies in `SL_3(F_q[t])`, because `F_q[t^(±1)] ∩ F_q[[t]] = F_q[t]`, and `Γ_0` has finite index
   in it.  So the index of `Δ` is finite.
3. *Bounded.*  The closure is compact, so `Δ` fixes a vertex `[L]` of the Bruhat-Tits building.  It then also
   fixes `[L]` under `e_ab(t^n F_q[[t]])`, and two such moves put `t^(2n) L_0` inside `L ⊆ L_0`.  Then
   `g L_0 ⊆ t^(-2n) L_0` for every `g` fixing `L`, which is the pole bound.
4. *(L2).*  In case 1, `Δ_m ∩ E_3(A_m)` has finite index in `E_3(A_m) = SL_3(A_m)`, and `t` is a monomial unit
   of `A_m`, so (Z3) of the normalised node gives `e_ab(1) ∈ E_B`.

## Calibration

- `B = G`: `Δ_m = SL_3(A_m)`, case 1.  This matches (V5) of
  [[twisted-diagonal-cones-need-a-profinitely-invisible-core]].
- `B = U_k`: `Δ_m ⊆ SL_3(F_q[t])`, pole order `0`, case 2, and indeed `e_ab(1) ∉ U_k ⊆ 1 + M_3(𝔪^k)`.
- Case 2 does reach pole order `n`.  With `D = diag(1, 1, t^n)`, the stabiliser `D K D^-1` has `(a, b)` entries
  in `t^(α_a - α_b) F_q[[t]]`, `α = (0, 0, n)`.  It contains `Γ_0 = E_3(t^n F_q[t])`, because `n + α_b - α_a ≥ 0`,
  and it contains `e_13(t^-n)`.  So `< Γ_0, e_13(t^-n) >` is bounded with pole order `n`.  We do not know
  whether `2n` itself is ever reached; the proof needs only some bound.
- *Bounded lines do not bound `E_B`.*  For `w ∈ R^d_(>0)` and the monomial valuation `v_w`, the group
  `E_w = { g ∈ SL_3(R) : v_w(g - 1) > 0 }` contains `U_k`, avoids `e_ab(1)`, and has pole order `0` on every
  monomial line.  It still contains Laurent elements such as `e_12(x_1^-1 x_2^N)` with `N w_2 > w_1`.  So (L1)
  alone cannot kill the level class.  Its Laurent part enters only off the lines.

## What is left

A level-containing certificate `B ⊇ U_k` for `T_3` now needs `E_B` with the properties of the normalised node
(span `M_3(A_B)` with `x_l^(±c) ∈ A_B`, not normalised by `E_3(A_B)`, infinite index against every `E_3(A')`
with a monomial unit).  In addition, every line section `Δ_m`, `m ∈ N^d \ {0}`, must fix a lattice between
`t^(2n) L_0` and `L_0`.  So the Laurent monomials of `A_B` must enter `E_B` only through elements not supported
on one monomial line, as in `E_w`.  The natural next invariant is a monomial valuation `v_w` with
`E_B ⊆ E_w`-type bounds.  The next step is to show that the compressors of an infranormal `C` preserve such a
valuation, which would contradict (W2) of [[nonneg-generated-kazhdan-groups-have-nonsalient-cones]].
