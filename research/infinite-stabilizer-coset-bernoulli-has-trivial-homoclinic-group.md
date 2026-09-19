---
rg: 2
id: infinite-stabilizer-coset-bernoulli-has-trivial-homoclinic-group
kind: claim
title: An infinite-stabilizer coset Bernoulli shift has trivial homoclinic group
distinct_from:
  dense-homoclinic-algebraic-actions-are-ce: that proves Connes embeddability when homoclinic points are dense; this computes the opposite extreme for coset shifts and shows why that theorem does not dispose of the Mihailova candidate.
  mihailova-nonseparable-coset-stabilizer: that constructs the specific infinite nonseparable stabilizer; this is the general dynamical calculation for every infinite stabilizer.
---

Let `Lambda` be countable, let `P<Lambda` be infinite, let `F` be a nontrivial
finite group, and let `Lambda` act by coordinate shifts on

```text
K=F^(Lambda/P).
```

Then the homoclinic group of this compact profinite action is trivial:

```text
Delta(K,Lambda)={1}.                                  (ICH1)
```

Thus the dense-homoclinic Connes-embedding criterion does not apply to any
nontrivial infinite-stabilizer coset Bernoulli shift.  In particular it does
not kill the Mihailova module of
`mihailova-nonseparable-coset-stabilizer`; that candidate sits at the exact
opposite endpoint from the regular Bernoulli shift.
