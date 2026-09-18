---
rg: 2
id: radu-bmw-lattice-is-mf
kind: claim
title: Radu's non-residually-finite BMW lattice is MF, so the mark (xz)^4 survives in operator-norm models and the product-of-trees core of the smallest Titz--Witzel kernel carries no MF obstruction
distinct_from:
  radu-bmw-lattice-sofic: that asks for permutation approximations of the same lattice, which stays open; this gives operator-norm corona approximations, which say nothing about Hamming or trace approximations.
  radu-commutator-collapse: that asserts Hamming collapse of [y(xz)^2y, xz] along almost actions; this proves the operator-norm analogue false, so any proof of that claim must use the normalized Hamming or trace structure.
  titz-witzel-residual-is-mf: that asks whether a whole Titz--Witzel residual is MF; this settles only the Radu sublattice pi_1(S_R) inside the smallest residual, and removes it as a source of a non-MF certificate.
  radu-mark-survives-only-if-horizontal-group-embeds: that proves no amenable quotient of the lattice keeps the mark; this keeps the mark in an operator-norm model of the lattice itself.
---

**ESTABLISHED.** Let `Γ_R = <a,b,c,x,y,z | a^2,b^2,c^2,x^2,y^2,z^2, axax, ayay, azbz, bxbx, bycy, cxcz>`
be Radu's BMW lattice (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`), and put `δ = xz`.

1. **MF.** `Γ_R` embeds in the unitary group of a norm-matrix corona. So `Rad_MF(Γ_R) = 1`,
   and `Rad_MF(π_1(S_R)) = 1` for the index-four subgroup `π_1(S_R)` (the fundamental group of Radu's square complex), which embeds in the smallest
   Titz--Witzel kernel `K = Γ_1^2`.
2. **The mark survives.** The non-residual-finiteness mark `δ^4` lies in the finite residual but
   not in `Rad_MF(Γ_R)`. There are unitary tuples `(a_n, ..., z_n)` with all twelve relator
   defects tending to `0` in operator norm and `limsup_n ||δ_n^4 - 1|| > 0`.
3. **No operator-norm commutator collapse.** Along the same tuples,
   `limsup_n ||[y_n δ_n^2 y_n, δ_n] - 1|| > 0`. So the operator-norm analogue of
   `radu-commutator-collapse` is false.

**Consequence for the Titz--Witzel MF question.** The non-residual finiteness of `K` is carried by
the Radu product-of-trees core. That core is MF, and its mark survives operator-norm
approximation. Two classes of arguments therefore cannot prove "`K` is not MF", which is the open
clause of `titz-witzel-exact-kazhdan-mf-radical-over-z`:
- an argument through a non-MF subgroup located in the core;
- a robust transfer of the exact-quotient chain "commutator dies ⇒ `δ^4` dies" to operator norm.

Any such proof must use the part of the building outside `π_1(S_R)`, or property (T) of `K`.

Proof in `radu-bmw-lattice-is-mf-proof`.
