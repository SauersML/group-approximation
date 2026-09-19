---
rg: 2
id: fixed-rectangular-kernel-unnamed-return-compiler
kind: claim
title: Compile an unnamed return as the kernel of one fixed rectangular group-algebra pencil
distinct_from:
  fanizza-matrix-coordinate-source-full-compression: that permits a matrix-coordinate decoder whose selected compression is not a fixed group-algebra factorization; this is the tempting strictly fixed rank-nullity specialization.
  fixed-rank-index-authenticator-has-gap-or-functoriality: that studies authentication by reading a hard rank; this asks rectangularity to force the rank automatically and uses a factorization to return the resulting unnamed kernel.
---

**REFUTED IMPLEMENTATION TARGET.**  Find a finitely presented group
`Gamma`, an infinite-order word `w`, integers `p>q`, and fixed matrices

```text
A in M_(q,p)(C[Gamma]),       C in M_(p,q)(C[Gamma])
```

with

```text
I_p tensor (w^2-1)=C A.                                (FRC1)
```

For every matrix model, the kernel of `A` would have density at least
`(p-q)/p`, and `(FRC1)` would make it an unnamed square-return carrier.

This target is refuted by
`fixed-rectangular-kernel-return-factorization-is-impossible`: von Neumann
rank-nullity produces the same positive kernel in the left regular factor,
where an infinite-order regular shift has no fixed vector.

## Attempts

- **One fixed rectangular pencil.**  This is exactly `(FRC1)`.  It dies in
  the regular representation before any approximation issue arises: the
  forced positive Murray--von Neumann kernel cannot lie in the zero kernel of
  an infinite-order bilateral shift difference.
- **Surviving boundary.**  A matrix-coordinate pencil selected only after
  inspecting the finite model, or a dimension-growing bounded-overlap family,
  is not covered.  Those alternatives are deliberately left to
  `fanizza-matrix-coordinate-source-full-compression` and the extensive
  syndrome/compiler routes rather than hidden inside this refuted fixed
  specialization.
