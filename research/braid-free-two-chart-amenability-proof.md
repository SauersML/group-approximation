---
rg: 2
id: braid-free-two-chart-amenability-proof
kind: route
title: Identify the separated root actor and apply the regular Følner representation
target: braid-free-two-chart-actor-is-amenable
requires:
  - jacobi-drifted-braid-defect-is-extensive
---

The two root groups are copies of the abelian group `(R,+)`.  Because they
act on different chart summands, they commute.  The only remaining mixed
relation is

```text
F U^+(r) F^(-1)=U^-(r),             F^2=1.
```

This is exactly `(R,+)^2 semidirect C_2`, proving `(BFA1)` and amenability.
An abelian or Heisenberg Weyl group `N` is nilpotent and amenable; extensions
of amenable groups are amenable, so `(BFA2)` is amenable.

Take a Følner sequence in `(BFA2)`.  Its normalized indicator vectors in the
left regular representation are almost invariant.  If `N` is infinite, that
regular representation has no nonzero `N`-fixed vector: an `N`-fixed
function is constant on every left `N`-coset, and a nonzero constant on an
infinite coset is not square summable.  Relative property `(T)` would turn
the almost invariant vectors into a nonzero `N`-fixed vector, a
contradiction.

