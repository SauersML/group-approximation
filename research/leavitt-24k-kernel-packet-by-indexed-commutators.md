---
rg: 2
id: leavitt-24k-kernel-packet-by-indexed-commutators
kind: route
title: Authenticate coefficient products by distinct-index commutators and evaluate the four-word packet
target: leavitt-24k-kernel-packet-excludes-scalar-field-models
requires:
  - binary-leavitt-units-generated-by-c3-and-c2-cubed
artifacts:
  - research/artifacts/leavitt-24k-finite-coefficient-kernel-packet-2026-09-08.md
---

The prerequisite supplies the marked map from `C_3*C_2^3`. In the
native Leavitt ring, `ts=1` gives `d=x_13(1)`, and cyclic conjugation
and one further commutator give `h=x_32(1)` and `a=x_12(1)`.
Every later product uses the identity
`[x_ij(r),x_jk(q)]=x_ik(rq)` with `i,j,k` pairwise distinct.
Same-root products add coefficients because the corresponding matrix
unit squares to zero. No analogous algebraic interpretation is imposed
on arbitrary group models.

The exact resulting coefficients are `v^2+1`, `tvs`, and
`st+vstv+1`; the prefix relations make all three zero. The old word
`r_*` is the square of the product of coordinate transposition `(12)`
and cycle `(123)`, so it also vanishes. Straight-line length accounting
gives the four stated bounds.

At `s=alpha,t=alpha^(-1),v=1`, the latter two coefficients equal one.
A nonidentity element has trace zero in a finite group's left regular
representation, hence defect `sqrt(2)`. For an arbitrary scalar-field
assignment, retain `z=ts` throughout instead of replacing it by one:
`d=x_13(z)`, `a=x_12(z^2)`, `w=x_32(sz^2)`, and therefore
`R_0=x_12(tvs z^2)`. Nonzero field coefficients cannot make this the
identity. The artifact proves each matrix identity explicitly.
