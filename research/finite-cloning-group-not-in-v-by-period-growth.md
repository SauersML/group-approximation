---
rg: 2
id: finite-cloning-group-not-in-v-by-period-growth
kind: route
title: "The bit-register cloning group has a non-coCF f.g. subgroup, and f.g. subgroups of V are coCF, so it does not embed in V"
target: some-finite-cloning-system-group-does-not-embed-in-v
requires:
  - some-finite-cloning-system-group-is-not-locally-cocf
---

Let `T` be the Thompson-like group of the bit-register cloning system on the finite groups `G_n = Sym({0,1}^n)`.
Let `Γ ≤ T` be the finitely generated, non-coCF subgroup given by
`finite-cloning-group-not-locally-cocf-by-period-growth`.

Suppose `ι: T → V` is an injective homomorphism. Then `ι(Γ) ≅ Γ` is a finitely generated subgroup of `V`. That makes
it coCF, by the following two imports, which is a contradiction.

Imports, quoted verbatim:
- J. Lehnert, P. Schweitzer, *The co-word problem for the Higman-Thompson group is context-free*, arXiv:math/0507090,
  abstract: "We use this method to show, that the Higman-Thompson groups, and therefore the Houghton groups, have
  context-free co-word problem." Thompson's `V` is the Higman–Thompson group `V_(2,1)`.
- R. Berns-Zieve, D. Fry, J. Gillings, H. Hoganson, H. Mathews, arXiv:1407.7745v2, §1, p. 1: "If the co-word problem
  of G is a context-free language, then we say G is coCF. This property does not depend on the choice of monoid
  generating set. The class of coCF groups was first studied by Holt, Rees, Röver, and Thomas [6]. They showed that the
  class is closed under taking finite direct products, taking restricted standard wreath products with virtually free
  top groups, and passing to finitely generated subgroups and finite index overgroups." Here [6] is J. London Math.
  Soc. 71 (2005) 643–657.

So `T` does not embed in `V`.

The same holds without the HRRT import. BBIP (arXiv:2601.13058, Thm 6.2(b)) give `p_V(n) ≍ exp(n^2)`, and their
Lemma 1.1(a) says period growth is monotone under embedding. These are incompatible with
`ord(w_s) ≥ 2^(2^s−2)/3` at `‖w_s‖ ≤ 248 s^3`.
