---
rg: 2
id: coset-bernoulli-action-is-essentially-free
kind: claim
title: Every nontrivial element of SL3(Z[1/3]) moves infinitely many SL3(Z)-cosets, so the coset Bernoulli action is essentially free
artifacts:
  - research/artifacts/coset-wreath-cartan-entropy-2026-08-22.md
distinct_from:
  coordinate-action-not-sofic: that is the Kun-Thom refutation of SOFIC approximability of the coset SET action; this is a pointwise dynamical statement about the p.m.p. Bernoulli extension - trivial a.e. stabilizers - proved by building geometry, with no approximation content.
  infinite-stabilizer-coset-bernoulli-has-trivial-homoclinic-group: that computes the homoclinic group of the algebraic-action avatar in the envelope lane; this establishes essential freeness of the measure action itself, the hypothesis Feldman-Moore needs to make the lamp algebra a Cartan masa.
---

Let `Lambda = SL_3(Z) <= Gamma = SL_3(Z[1/3])`, `I = Gamma/Lambda`, and
let `Gamma` act on `X = {-1,1}^I` with the Bernoulli(1/2) product
measure by permuting coordinates.  Claim, in two strengthenings:

1. every `g != 1` in `Gamma` moves infinitely many cosets in `I`;
2. consequently `mu(Fix_X(g)) = 0` for every `g != 1`, i.e. the
   generalized Bernoulli action `Gamma acts (X, mu)` is essentially
   free (almost every stabilizer is trivial).

Proof mechanism (full details in the artifact): `I` is
`Gamma`-equivariantly the set of type-0 vertices of the Bruhat–Tits
building of `SL_3(Q_3)` (vertex stabilizer computation plus strong
approximation); an isometry fixing cofinitely many type-0 vertices
fixes, in every apartment, arbitrarily large lattice triangles around
every point, hence — fixed sets being convex in CAT(0), apartments
convex in the building — acts trivially, and the kernel of the building
action is `mu_3(Q_3) = 1`.  Independence of disjoint orbit-constancy
events then kills the measure of `Fix_X(g)`.

**Scope: every prime.**  The argument is uniform in `p` for
`(SL_3(Z[1/p]), SL_3(Z))`: the building of `SL_3(Q_p)` and strong
approximation work verbatim, and the endgame needs only
`Gamma cap Z(SL_3(Q_p)) = mu_3(Q) = 1` — the element produced by the
convexity argument lies in `Gamma <= SL_3(Q)`, so even for
`p = 1 mod 3` (where `mu_3(Q_p)` is nontrivial) the fixed-cofinitely
element is trivial.  In particular the p = 2 wreath — the home of the
constructive flat-tower probes — carries the identical freeness,
Cartan, and entropy-ceiling package, so the moduli-flip discipline of
`coset-wreath-hyperlinearity-forces-strong-one-boundedness` binds those
probes too.  The same argument on the `(p+1)`-regular tree gives the
`SL_2(Z[1/p])` statement modulo the center `{+-1}` (which acts
trivially on `I`): the `PSL_2` coset Bernoulli action is essentially
free.

This is the freeness input that makes the lamp algebra
`L^infinity(X)` a Cartan masa in `L(W_3)`
(`coset-wreath-algebra-has-a-lamp-cartan`) and thereby activates the
free-entropy constraint of
`coset-wreath-hyperlinearity-forces-strong-one-boundedness`.
