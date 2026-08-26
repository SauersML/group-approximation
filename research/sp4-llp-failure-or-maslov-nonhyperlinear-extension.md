---
rg: 2
id: sp4-llp-failure-or-maslov-nonhyperlinear-extension
kind: claim
title: Either the full Sp4 group C-star algebra fails LLP or a finite Deligne cover is nonhyperlinear
distinct_from:
  sp2g-z-full-c-star-algebra-has-llp: that asks which side of the lifting fork holds; this proves an unconditional disjunction whose other side is the nonhyperlinear-group endpoint.
  sp4-small-maslov-twisted-group-factors-are-ce: that is the CE side of the Maslov parameter dichotomy; this records the consequence of both possible answers.
---

**ESTABLISHED DICHOTOMY.** At least one of the following statements holds:

1. `C^*(Sp_4(Z))` does not have the local lifting property;
2. a finitely presented finite cyclic Deligne cover of `Sp_4(Z)` is
   nonhyperlinear.

Indeed let `E_CE` be the closed subgroup of the Maslov circle from
`maslov-ce-parameter-set-is-a-closed-subgroup`.

If `E_CE=R/Z`, choose any nontrivial null sequence `theta_n->0`. Jiang's
Bernoulli injection supplies nontrivial measurable cocycles, and the twisted
Bernoulli CE equivalence supplies the Connes-embeddable crossed products.
Ioana--Spaas--Wiersma Theorem C then says that `C^*(Sp_4(Z))` fails LLP.

If `E_CE` is finite, choose a prime `q` not dividing its order. Then
`1/q notin E_CE`, and
`maslov-ce-subgroup-classifies-finite-deligne-covers` makes the finite
central extension `E_q` nonhyperlinear. Since it is a finite central
extension of the finitely presented lattice, it is finitely presented.

Thus the only way the Sp4 LLP route can remain positive is for the second,
group-theoretic alternative already to solve the nonhyperlinear existence
problem.
