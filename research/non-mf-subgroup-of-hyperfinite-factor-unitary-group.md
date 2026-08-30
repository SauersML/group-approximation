---
rg: 2
id: non-mf-subgroup-of-hyperfinite-factor-unitary-group
kind: claim
title: Some countable non-MF group embeds in the unitary group of the hyperfinite II1 factor
distinct_from:
  hyperfinite-factor-qd-forces-unitary-subgroups-mf: that is the established implication "R quasidiagonal ⟹ unitary subgroups MF"; this is the existence of a witness that, through that implication, would refute X(2).
  literal-group-factorization-property: that asks for amenability of the canonical trace of C*(E), a property of one specific character (the regular one, whose GNS closure is the non-hyperfinite L(E)); this asks for any non-MF group with a faithful character of hyperfinite GNS closure, a different character on a possibly different group.
  non-hyperlinear-group: that asks for a group with no Hilbert--Schmidt approximation at all; this asks for a group with the strongest Hilbert--Schmidt structure (an honest embedding into R) that nevertheless has no operator-norm approximation.
artifacts:
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
---

There is a countable group `Γ` that is not MF and admits an injective
homomorphism `Γ → U(R)`; equivalently, a countable non-MF group with a
faithful character `τ` (`τ(g) ≠ 1` for `g ≠ 1`) whose GNS closure is a
hyperfinite von Neumann algebra.

By `hyperfinite-factor-qd-forces-unitary-subgroups-mf` such a `Γ` makes
`C*(Γ) ⊆ R` a separable non-quasidiagonal subalgebra, so `R` is not
quasidiagonal and Problems X(2) and X(1) of Schafhauser--Tikuisis--White are
refuted (`hyperfinite-factor-not-qd-via-non-mf-unitary-subgroup`).

What the witness must look like.  It cannot be residually finite or
amenable (those are MF).  It cannot be finitely generated with property (T)
(`kazhdan-groups-in-hyperfinite-unitary-group-are-rf`): its faithful
hyperfinite character would be a limit of finite-dimensional characters and
the group would be residually finite.  So the witness must be a non-Kazhdan,
non-residually-finite, non-amenable group carrying a faithful hyperfinite
character, and must be non-MF.  The only non-MF groups currently known
(the one-sided compression family of `non_mf_groups_exist.tex` and
Eckhardt's generalized wreath products) all contain a Kazhdan subgroup `L`
with a compressor; the obstruction applies to `L` and forces `L` to be
residually finite, which is consistent with `L = Z^3 ⋊ SL_3(Z)` in the
literal group `E`.

## Attempts

* **Kazhdan non-MF groups.**  `H` and `Q` are Kazhdan; dead by
  `kazhdan-groups-in-hyperfinite-unitary-group-are-rf`
  (route `non-mf-unitary-subgroup-via-kazhdan-non-mf-groups`).
* **The Clifford witness `W = Cl(X) ⋊ Σ` and the block-commuting quotient
  of `E`.**  Dead: `clifford-witness-has-no-hyperfinite-marked-representation`
  (route `non-mf-unitary-subgroup-via-clifford-witness`).  With the sign at
  `−1` the lamps generate a UHF algebra with unique trace, the site
  permutations act outerly on its hyperfinite completion, and
  `hyperfinite-covariant-obstruction-lemma` forces the regular character on
  `Σ ⊇ SL_3(Z)`, which is not amenable.  So the mark is invisible to
  hyperfinite representations of these groups, exactly as it is invisible to
  norm-matrix coronas.
* **The literal group `E`.**  `E` is sofic (`literal-group-sofic`), so
  `E ↪ U(R^ω)`; the question is whether the ultrapower can be replaced by
  `R` itself.  Reduced in `literal-group-embeds-in-hyperfinite-unitary-group`
  to two pieces: a hyperfinite representation of `E` sending the central
  mark `w` to `−1` (a projective hyperfinite representation of `E/<w>` with
  the extension cocycle), and a faithful hyperfinite character of `E/<w>`.
  Neither is known.  Every finite-dimensional representation of `E` kills
  `w` (finite-dimensional representations are MF), so the marked
  representation must be genuinely infinite-dimensional, with no
  finite-dimensional approximants of its character in operator norm; it
  may still have them in Hilbert--Schmidt norm, which is what `R` requires.
* **Why the compression criterion does not obstruct.**  Inside `R` the
  Kazhdan projection of `ρ(L)` on `L²(R)` is the projection onto
  `L²(ρ(L)' ∩ R)`, and `ρ(t)` conjugates it to the projection onto
  `L²(ρ(tLt^{-1})' ∩ R) ⊇ L²(ρ(L)' ∩ R)`.  A von Neumann subalgebra of `R`
  can be properly contained in a unitary conjugate of itself (a shift on a
  tensor factorisation of `R`), so the finiteness step of the criterion,
  which needs a finite-dimensional matrix algebra, has no analogue in `R`.
  This is the same reason the criterion does not touch soficity.
