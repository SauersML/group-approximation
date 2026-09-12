---
rg: 2
id: binary-leavitt-nonzero-projectives-are-free
kind: claim
title: Every nonzero finitely generated projective module over the binary Leavitt algebra is free of rank one
distinct_from:
  agp-purely-infinite-simple-k1-is-unit-abelianization: that computes K_1 of purely infinite simple rings as the abelianized unit group; this is the nonstable K_0 statement that the monoid of projectives of L(1,2) is {0, [R]}, used to classify one-sided invertible elements, and neither statement gives the other.
artifacts:
  - research/artifacts/leavitt-kaplansky-pair-dichotomy-2026-09-12.md
---

**ESTABLISHED by citation.** For `R = L_K(1,2)` over any field `K`, every nonzero finitely
generated projective right `R`-module is isomorphic to `R_R`.

Source: Bergman's computation `V(L_K(1,n)) = <x | x = n x>` of the monoid of isomorphism classes
of finitely generated projectives (G. M. Bergman, *Coproducts and some universal ring
constructions*, Trans. AMS 200 (1974), Theorem 6.1). For `n = 2` the monoid is `{0, x}`. The
graph-algebra form is Ara--Moreno--Pardo, *Nonstable K-theory for graph algebras*, Algebr.
Represent. Theory 10 (2007), Theorem 3.5, for one vertex with two loops.

Its consumer is `leavitt-kaplansky-pairs-split-kernel-local-or-s0-lift` (Lemma 1 of the artifact):
every left-invertible non-unit `x` of `L_(F_2)(1,2)` equals `u s_0` for a unit `u`.
