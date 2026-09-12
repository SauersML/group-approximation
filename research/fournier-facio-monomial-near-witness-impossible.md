---
rg: 2
id: fournier-facio-monomial-near-witness-impossible
kind: claim
title: A Fournier--Facio hyperlinearity witness cannot normalize any charged basis
invalidates:
  - fournier-facio-monomial-banach-limit-witness
distinct_from:
  fournier-facio-compression-coset-charge-impossible: That uses the specific non-coamenable coset factor and does not need freeness; this excludes every monomial charged basis, even one unrelated to the compression cosets, by the group's established nonsoficity.
  binary-leavitt-has-no-normal-free-near-representation: That excludes normal states but permits nonmonomial singular witnesses; this allows singular charges but excludes exact basis normalization.
---

Let `G` be the explicit Fournier--Facio group.  There is no
Kahl--Schneider essentially free amenable near representation

```text
pi:G -> U(ell^2(X))
```

for which every `pi(g)` is monomial in the charged basis `X` (equivalently,
normalizes the diagonal algebra `ell^infinity(X)`).

The assertion allows arbitrary phases, arbitrary singular probability
charges on `P(X)`, and only charge-almost-everywhere multiplicativity.  Thus
no Schreier action, ultraproduct of Schreier actions, phase-twisted
quasi-regular representation, or Banach-limit of permutation blocks can be
the missing positive witness.  Any positive witness must mix basis vectors
genuinely on a set of positive charge; its invariant state cannot come from a
Cartan/monomial model.

