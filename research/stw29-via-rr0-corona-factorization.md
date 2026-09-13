---
rg: 2
id: stw29-via-rr0-corona-factorization
kind: route
title: The corona factorization property for simple real rank zero algebras settles Rordam's dichotomy
target: stw99-problem-xxix-rr0-dichotomy
requires: [rr0-simple-algebras-have-corona-factorization, opr-cfp-rr0-dichotomy]
---

Let `A` be a simple C\*-algebra of real rank zero.

*Separable case.*  By the premise `rr0-simple-algebras-have-corona-factorization`,
`A` has the CFP; by `opr-cfp-rr0-dichotomy` (OPR Corollary 5.16), `A` is
stably finite or purely infinite.

*General case.*  Suppose `A` contains a finite nonzero projection `q` and an
infinite projection `p` in some matrix algebra.  Take a separable
sub-C\*-algebra `A_0` containing `q`, the matrix entries of `p`, the partial
isometry witnessing infiniteness of `p`, and partial isometries witnessing
`p <= l q` in `V(A)`.  By separable inheritance of simplicity and of real rank
zero (Blackadar's separable inheritance), `A_0` can be enlarged to a separable
simple real-rank-zero sub-C\*-algebra `A_1`.  In `A_1`, `p` is still infinite
(the witnesses lie in `A_1`) and `q` is still finite (finiteness passes to
subalgebras containing the projection).  This contradicts the separable case.
Hence `A` has no finite nonzero projection or is stably finite.  In the first
case real rank zero puts an infinite projection in every nonzero hereditary
subalgebra, which is pure infiniteness for simple algebras.
