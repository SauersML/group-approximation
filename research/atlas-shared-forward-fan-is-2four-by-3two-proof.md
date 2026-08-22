---
rg: 2
id: atlas-shared-forward-fan-is-2four-by-3two-proof
kind: route
title: Tensor F2 module and Todd-Coxeter proof of the 144-state two-fan carrier
target: atlas-shared-forward-fan-is-2four-by-3two
requires: []
artifacts:
  - experiments/atlas_a4_shared_involution_completion.py
  - research/artifacts/atlas-a4-shared-forward-fan-completion.json
---

## Explicit lower bound

Let `A in GL_2(F2)` have order three, put

```text
V=F2^2 tensor F2^2,
R=A tensor I_2,
Z=I_2 tensor A,
```

and choose a nonzero pure tensor `v in V`.  In
`V semidirect <R,Z>`, take `r=(0,R)`, `z=(0,Z)`, and the translation
`b=(v,I)`.  The two linear maps commute and satisfy

```text
I+R+R^2=I+Z+Z^2=0.
```

Hence `(rb)^3=(zb)^3=1`.  The nine `<R,Z>` translates of `v` span `V`, so
these three elements generate all of `V semidirect (C3 x C3)`, of order 144.
This gives a quotient of `(A4-2FAN-1)` of order 144.  Restricting to either
`<r,b>` or `<z,b>` gives `C2^2 semidirect C3=A4`.

## Exact upper bound and structure

The Todd--Coxeter enumeration in the artifact gives order 144 for the
presentation itself, so the explicit quotient is an isomorphism.  Its exact
permutation representation has derived series orders `144,16,1`, with the
derived subgroup containing one identity and fifteen involutions; its
abelian invariants are `3,3`, and its center has order one.  This independently
confirms `(A4-2FAN-2)`.

Finally restriction of a regular representation to a subgroup is the subgroup
regular representation repeated by the index.  The indices of `C3^2`, either
`A4`, and `C2` in `C` are respectively `16,12,72`.  Multiplication by `140k`
proves every identity in `(A4-2FAN-3)` and the common-unitary construction in
the claim.
