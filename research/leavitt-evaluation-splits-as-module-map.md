---
rg: 2
id: leavitt-evaluation-splits-as-module-map
kind: claim
title: The Leavitt evaluation map splits as a module map
distinct_from:
  leavitt-evaluation-has-no-ring-section: that is the established no-go for a *ring* section of the same map; this asks only for a left-module section, which that argument does not touch
  left-invertible-lift-of-s0-in-leavitt-group-algebra: that is the element-level target this claim manufactures; this is the structural statement, strictly stronger and provable by different means
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

Prove that the evaluation map

    pi : S = F_2[G] ->> R = L_(F_2)(1,2),       G = R^x,

splits as a map of **left `S`-modules**: some `S`-linear `sigma : R -> S`
with `pi . sigma = id_R`.  Equivalently, `R` is projective as a left
`S`-module (it is cyclic, so projective and split are the same here), or
`ker(pi)` is a direct summand of `S`.

By `stable-finiteness-failure-from-module-splitting` this produces
`b a = 1 != a b` in `S` outright, hence disproves Gottschalk's conjecture for
`G`.

## Why "module" and not "ring"

A ring section is impossible: it would place a full binary Leavitt family
inside `F_2[G]`, which the augmentation forbids
(`leavitt-evaluation-has-no-ring-section`).  The entire content of this
claim is the distance between *direct summand* and *subring* — a module
section need not respect multiplication in `R`, and the no-go uses
multiplicativity at every step.

## Dynamical reading

Dualizing a splitting `S = sigma(R) (+) ker(pi)` gives an equivariant linear
complement to the proper subshift `X = ker(pi)^perp` inside the full shift.
That complement is exactly what is missing when one tries to extend the
strict self-embedding of `X` to the full shift; the impossibility of doing so
*without* such extra input is
`subshift-self-embedding-carries-no-surjunctivity-content`.

No evidence for or against this claim is known here.  It is recorded because
it is the cleanest structural sufficient condition, not because it is
believed.
