---
rg: 2
id: stw63-relative-k0-return-proof
kind: route
title: Cancel the two bidually equivalent corner classes
target: stw63-relative-k0-return-criterion
requires:
  - stw63-aue-is-relative-corner-equivalence
  - stw63-bidual-relative-corners-equivalent
---

The images of `p` and `q` are Murray--von Neumann equivalent in `E`, so
their `K_0(E)` classes agree.  Injectivity in (2) gives
`[p]=[q]` in `K_0(D)`.  By the definition of the Grothendieck group, there
is a projection class `r in V(D)` such that

```text
[p]+r=[q]+r in V(D).
```

Projection cancellation gives `[p]=[q]` in `V(D)`, hence `p` and `q` are
Murray--von Neumann equivalent in `D`.  The relative-corner theorem returns
an implementing unitary sequence in `B`.

For the stated sufficient specialization, stable rank one implies
projection cancellation.  One exact standard reference is Blackadar,
*K-Theory for Operator Algebras*, second edition, Proposition 6.5.1; its
proof approximates the partial isometry by an invertible and uses polar
decomposition.  The graph argument itself only imports the explicit
cancellation hypothesis.
