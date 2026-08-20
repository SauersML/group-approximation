---
rg: 2
id: hs-stable-finite-bi-index-kazhdan-pair-exists
kind: claim
title: There is an infinite finite-bi-index Kazhdan subgroup pair with a same-dimension HS-stable acting group
distinct_from:
  uniform-hs-site-coherence-for-finite-bi-index-pair: that states the operational rounding property needed by the Clifford tape; this asks for a structural package which implies it by a separate theorem.
  ck-envelope-simple-core-has-finite-bi-index: that asks to alter one Boone--Higman envelope so its simple core has finite bi-index; this additionally requires a Kazhdan stabilizer and normalized-HS stability of the ambient acting group.
---

Find an explicit finitely presented group `L` and an explicit finitely
generated infinite-index subgroup `H<L` such that

```text
|H\L/H| < infinity,
H has property (T),
L is same-dimension normalized-HS stable.                         (HFK1)
```

The stability statement must have a quantitative modulus uniform over matrix
dimension and must remain valid after restriction to an almost invariant
positive-density spectral block.

## Attempts

- Finite stabilizers are unusable: in an infinite transitive finite-rank
  action a finite point stabilizer cannot be transitive on an infinite
  off-diagonal orbit.
- Standard arithmetic parabolics have a finite Bruhat decomposition over the
  ambient field, but their intersections with finitely generated arithmetic
  groups generally acquire infinitely many integral double-coset invariants.
- Known finitely presented highly transitive groups provide finite pair-orbit
  actions, but no same-dimension normalized-HS stability theorem for the
  acting group or Kazhdan theorem for the point stabilizer is available.
- Higher-rank stability candidates provide the right spectral rigidity, but
  no explicit infinite-index finite-bi-index Kazhdan subgroup has been
  identified in them.

