---
rg: 2
id: arithmetic-router-permanence-no-go-proof
kind: route
title: Use trivial amenable radicals and full MF radical to fence off the standard positive classes
target: arithmetic-router-permanence-no-go
requires:
  - two-generated-single-element-hull-router
  - concrete-compression-source
  - arithmetic-single-defect-saturation
  - torsion-free-hyperbolic-kazhdan-partner-exists
  - cprime-one-sixth-presentations-are-hyperlinear
artifacts:
  - research/artifacts/arithmetic-single-defect-saturation-2026-08-23.md
---

## The partner kernel

Use the primary partner from
`torsion-free-hyperbolic-kazhdan-partner-citation`: a torsion-free cocompact
lattice `H < Sp(2,1)`.  It is non-elementary hyperbolic.  Every amenable
normal subgroup of a non-elementary hyperbolic group is finite: an amenable
subgroup is elementary, and an infinite elementary normal subgroup would
give the whole group a finite boundary orbit and make it elementary.
Torsion-freeness therefore gives

```text
AmenableRadical(H) = 1.                                  (AHK2)
```

Suppose `ker(q_H)` were amenable.  By `(AHK2)` it would be trivial, so
`q_H` would identify `Q` with `H`.  But this lattice is a finitely generated
linear group and hence residually finite, whereas arithmetic defect
saturation gives the nontrivial group `Q` full MF radical.  A nontrivial
residually finite group is MF and has trivial MF radical (the identity map to
itself separates every nonidentity element).  This contradiction proves
that `ker(q_H)` is nonamenable.

## The arithmetic-source kernel

The amplified source is the nondegenerate free product

```text
R = E * F_2,
```

with both factors nontrivial and torsion-free.  A nontrivial amenable normal
subgroup of such a free product cannot exist.  Indeed the Bass--Serre action
has trivial edge stabilizers.  A normal subgroup containing a hyperbolic
element has infinitely many independent conjugates and is nonamenable; a
normal subgroup containing only elliptic elements fixes the invariant
minimal subtree pointwise and is trivial.  Equivalently, the amenable radical
of a nondegenerate free product other than `C_2 * C_2` is trivial.  Thus

```text
AmenableRadical(R) = 1.                                  (AHK3)
```

If `ker(q_R)` were amenable, `(AHK3)` would make `q_R` an isomorphism.  Then
the Kazhdan group `Q` would be the nontrivial free product `E * F_2`.  This is
impossible: property `(T)` implies Serre's property `FA`, while the canonical
Bass--Serre action of `E * Z` has no global fixed point.  Hence
`ker(q_R)` is nonamenable.

## Exact finite models

By `arithmetic-single-defect-saturation`, `Q` is nontrivial and

```text
Rad_MF(Q) = Q.                                           (AHK4)
```

If `Q` were LEF, finite presentability would upgrade sufficiently large exact
local multiplication tables to genuine homomorphisms into finite groups;
therefore `Q` would be residually finite.  Residual finiteness implies MF and
forces the MF radical to be trivial, contradicting `(AHK4)`.  This proves at
once that neither exact finite-ball models nor genuine finite quotients can
be the required permutation construction.

Finally, `cprime-one-sixth-presentations-are-hyperlinear` records the stronger
literature chain for a finite classical `C'(1/6)` presentation: cubulation,
hyperbolicity, virtual specialness, and residual finiteness.  The same last
step applies if virtual specialness is obtained by any other method.  Either
conclusion contradicts `(AHK4)`.  Hull's relative small-cancellation theorem
therefore cannot be replaced here by a classical `C'(1/6)` or virtually
special certificate.  Its finite-ball protection changes the quotient when
the protected ball changes and supplies no exact local models of one fixed
`Q`.

What survives all these fences is precisely the open claim
`arithmetic-defect-saturated-kazhdan-group-is-sofic`: approximate permutation
models with a vanishing Hamming exceptional set, not exact local embeddings.
