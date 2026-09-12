---
rg: 2
id: mf-representations-of-units-extend-under-stabilization
kind: claim
title: Over a purely infinite simple ring every MF representation of the units extends uniquely to every matrix rank
distinct_from:
  purely-infinite-unit-group-max-mf-quotient-is-k1: that computes the maximal MF quotient at rank one; this is the restriction bijection between ranks, which is what that computation implies once it is applied at every rank.
  aut-of-projective-module-max-mf-quotient-is-k1: that says the quotient is the same for every projective module; this compares the two Hom sets along one fixed inclusion and asserts a bijection, not merely an abstract isomorphism.
  finite-character-fails-to-extend-after-stabilization: that is the failure of the same extension property for a simple stably finite ring; the two together locate the phenomenon in pure infiniteness.
artifacts:
  - research/artifacts/k1-classification-and-extension-bridge-2026-09-07.md
---

Let `R` be a countable unital purely infinite simple ring, `M` an MF group,
`n >= 1`, and

```text
iota_n : R^x -> GL_n(R),   u |-> diag(u,1,...,1).
```

Then restriction along `iota_n` is a bijection

```text
Hom(GL_n(R), M) --> Hom(R^x, M).
```

Every homomorphism of the unit group to an MF group extends to every matrix
rank, and the extension is unique.

For `R = L_k(1,2)` both sides are trivial, so the statement specializes to
the total collapse of that family.
