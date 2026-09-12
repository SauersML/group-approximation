---
rg: 2
id: aut-of-projective-module-max-mf-quotient-is-k1
kind: claim
title: The maximal MF quotient does not depend on which nonzero projective module is used
distinct_from:
  purely-infinite-unit-group-max-mf-quotient-is-k1: that is the statement for the free module of rank one; this says the answer is the same for every nonzero finitely generated projective module, so matrix rank is a coordinate choice and not a parameter.
  unit-group-is-automorphisms-of-a-self-doubling-module: that describes one unit group as automorphisms of a self-doubling module and needs the copies to exhaust it; this is a statement about the MF quotient for every projective module over a purely infinite simple ring.
artifacts:
  - research/artifacts/k1-classification-and-extension-bridge-2026-09-07.md
---

Let `R` be a countable unital purely infinite simple ring and let `P` be any
nonzero finitely generated projective right `R`-module.  Then

```text
Aut_R(P) / Rad_MF(Aut_R(P)) = K_1(R).
```

In particular this covers `GL_n(R)` for every `n >= 1` and every nonzero
idempotent corner.  Rank is a choice of coordinates in the construction, not
a parameter in the conclusion.
