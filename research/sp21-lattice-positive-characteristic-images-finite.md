---
rg: 2
id: sp21-lattice-positive-characteristic-images-finite
kind: claim
title: A cocompact Sp(n,1) or F4(-20) lattice has only finite linear images in positive characteristic
distinct_from:
  normal-subgroups-of-arithmetic-lattices-are-congruence-open: that controls congruence quotients through strong approximation in characteristic zero; this excludes every infinite linear image over fields of positive characteristic, arithmetic or not
  sp21-lattice-has-congruence-subgroup-property: that is the open claim that essentially all finite quotients are congruence; this only removes infinite characteristic-p linear images, and says nothing about finite quotients
---

**ESTABLISHED.** Let `Γ` be a cocompact lattice in `Sp(n,1)` (`n >= 2`) or in
`F_4^(-20)`. Let `K` be a field of characteristic `p > 0`. Then every homomorphism
`ρ: Γ -> GL_m(K)` has finite image.

**Why it matters for Gromov's question.** A finite simple quotient of Lie type in
characteristic `p` is a finite image, so this alone says nothing about it.
Families of such quotients are another matter: along an ultrafilter they
assemble into a linear representation, and this claim kills every family of
fixed characteristic `p` and bounded rank. That is the positive-characteristic
half of `sp21-bounded-rank-simple-quotients-almost-all-congruence`.

Proof in `sp21-lattice-positive-characteristic-images-finite-proof`. The inputs
are Schur's theorem, Tits' embedding lemma and the Gromov--Schoen fixed-point
theorem for Euclidean buildings. This is a standard consequence of nonarchimedean
superrigidity; no novelty is claimed. Not Lean-verified.
