---
rg: 2
id: literal-group-embeds-in-hyperfinite-unitary-group
kind: claim
title: The literal group E has a faithful character with hyperfinite GNS closure
distinct_from:
  literal-group-sofic: that gives permutation models, hence an embedding of E into U(R^ω) through the ultrapower; this asks for an embedding into R itself, a single hyperfinite representation with no ultrafilter.
  literal-group-factorization-property: that concerns the canonical (regular) character of E, whose GNS closure L(E) is not hyperfinite; this asks for a different, faithful character with hyperfinite GNS closure.
  literal-mark-quotient-mf: that asks for operator-norm matrix models of E/<w>; this asks for a Hilbert--Schmidt-exact object, an embedding of E into R, and the mark must survive, which no operator-norm model allows.
artifacts:
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
---

The literal finitely presented group `E` of `non_mf_groups_exist.tex`
(Definition `def:E` of `non_mf_group_notes.tex`: generators
`v_1, v_2, v_3, x, y, z, t, c`, base `B = Z^3 ⋊ SL_3(Z)`, compressor `t`
doubling the translations, commuting involution `c`, central mark
`w = [tct^{-1}, v_1 (tct^{-1}) v_1^{-1}]`) admits an injective homomorphism
`E → U(R)`.

Since `E` is not MF (`literal-group-fails-mf-conventions`), this would make
`E` a witness for `non-mf-subgroup-of-hyperfinite-factor-unitary-group` and
refute STW Problems X(2) and X(1).

**Splitting.**  Let `w` be the mark.  A faithful character `τ` with
hyperfinite GNS closure `M` has `ρ(w)` a central involution of `M` with
`τ(w) ≠ 1`, so `M = pM ⊕ (1−p)M` with `ρ(w) = 1` on `pM` and `−1` on
`(1−p)M`, `p ≠ 1`.  Conversely `τ = ½(τ_1 + τ_2)` is a faithful hyperfinite
character of `E` whenever

1. `τ_1` is a faithful hyperfinite character of `E/<w>` pulled back to `E`
   (faithful on `E` away from `w`), and
2. `τ_2` is any hyperfinite character of `E` with `τ_2(w) = −1`, i.e. a
   homomorphism `E → U(N)`, `N` hyperfinite finite with faithful normal
   trace, sending `w` to `−1` (a projective hyperfinite representation of
   `E/<w>` with the extension cocycle of `1 → <w> → E → E/<w> → 1`).

`τ(w) = 0 ≠ 1`, and `τ(g) = 1` forces `τ_1(g) = 1`, so `g ∈ {1, w}`.

## Attempts

* **Reduction to invariant marked characters of the free amalgam.**  With
  `E = C(𝒢) ⋊ Σ` and `ρ(w) = −1`, the trace of `W` restricts to a
  `Σ`-invariant character `τ_Λ` of the lamp kernel `Λ = C(𝒢)` (a central
  amalgam of order-512 Clifford blocks,
  `literal-lamp-kernel-clifford-block-amalgam`) with `τ_Λ(w) = −1` and
  hyperfinite GNS closure `M`.  By
  `hyperfinite-covariant-obstruction-lemma`, if every `g ∈ Σ \ {e}` acts
  properly outerly on `M` then `Σ` would be amenable, which it is not.  So
  a faithful hyperfinite character of `E` needs a `Σ`-invariant hyperfinite
  marked character of `Λ` on whose GNS closure some `g ≠ e` is inner on a
  nonzero central piece.  Three families are dead: (i) the canonical
  character of any `Σ`-invariant quotient of `Λ` in which some pair of
  blocks does not commute has non-injective GNS closure (it contains a free
  product `M_16 * M_16`, an interpolated free group factor); (ii) the
  block-commuting quotient is `clifford-witness-has-no-hyperfinite-marked-representation`;
  (iii) the direct-integral characters `∫ tr_16 ∘ ρ_ℓ dμ(ℓ)` over a
  `Σ`-invariant product measure on block labelings `ℓ : X → {1,…,8}` have
  type I closure `L^∞(Ω) ⊗ M_16` on which every `g ≠ e` acts essentially
  freely on the centre, hence properly outerly.  A fully inner `g`
  (`ρ(c_ξ) = ρ(c_{gξ})` for all `ξ`) is impossible: `Σ`-invariance spreads
  the identification to the normal closure `N` of `g`, every nontrivial
  normal subgroup of `Σ` contains a nontrivial translation, every nontrivial
  translation is conjugate into `K \ B`, and identifying two adjacent lamps
  kills `w`.  What remains open is partial innerness on a central piece for
  a general `Σ`-invariant hyperfinite marked character.

* **Finite-dimensional models.**  Every finite-dimensional unitary
  representation of `E` kills `w` (finite-dimensional representations are
  MF and `w` lies in the MF radical), so `τ_2` cannot be a limit of
  finite-dimensional characters in operator norm.  It may be a limit in
  Hilbert--Schmidt norm; a hyperfinite character is exactly a character
  with Hilbert--Schmidt-approximable, u.c.p.-liftable models
  (Brown, Theorem 3.2.2).  The sofic approximations of `E`
  (`literal-group-sofic`) send `w` to permutations at Hamming distance
  tending to `1` from the identity, so `w ↦ −1`-type behaviour is available
  in the ultrapower; the missing step is coherence of the block tower
  across levels, an honest representation into `R` rather than `R^ω`.
* **Kazhdan obstruction.**  The base `B = Z^3 ⋊ SL_3(Z)` is Kazhdan, so
  `τ|_B` must be a limit of finite-dimensional characters
  (`kazhdan-groups-in-hyperfinite-unitary-group-are-rf`); `B` is
  residually finite, so this is consistent.  It constrains `τ_2|_B` to be
  a limit of finite-dimensional characters of `B` while `τ_2(w) = −1`, and
  `w` is a commutator of two conjugates of `c`, which commutes with `B`.
* **Piece 1.**  `E/<w>` is not MF (`literal-mark-quotient-not-mf`), so
  its faithful hyperfinite character, if any, is itself a non-MF witness in
  `U(R)`; piece 1 alone would already refute X(2).  Its Hamming-metric
  behaviour is recorded in `literal-mark-quotient-not-stable-in-finite-actions`.
