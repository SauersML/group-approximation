---
rg: 2
id: infinite-edge-common-commutant-for-first-chord
kind: claim
title: Create the first chord target and its relative spectral transports in one infinite-edge extension
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  first-cycle-signed-hecke-chord: that asks for the resulting context atlas and preservation of all previous identities; this isolates the new group-theoretic data from which piecewise transport assembles the endpoint regauges.
  finite-relative-commutant-chord-is-bounded-integer-feasibility: that decides the finite-matrix double orbit; this asks for an algebraic common-commutant element and algebraic projection equivalences in an infinite signed group corner.
  finite-edge-hnn-closures-cannot-finish-the-nonce-atlas: that excludes iterations over finite associated subgroups; this explicitly permits a finitely generated infinite associated subgroup or a non-Bass--Serre presentation.
---

Use the first-chord data from `first-cycle-signed-hecke-chord`, with endpoint
separator atom algebras `A_0,A_1` and chord signs `X_0,X_1` in the join-tree
corner.  Construct a finitely presented extension group `Gamma` in which the
base group remains embedded, `q_D` remains nonzero, and there is an algebraic
self-adjoint involution

```text
Z in q_D C[Gamma]q_D intersect A_0' intersect A_1'.       (IEC1)
```

For each endpoint `i`, separator atom `e_(i,s)`, and sign
`epsilon in {+1,-1}`, require finite algebraic projection partitions

```text
e_(i,s)(1+epsilon X_i)/2=sum_k p_(i,s,epsilon,k),
e_(i,s)(1+epsilon Z)/2  =sum_k r_(i,s,epsilon,k),          (IEC2)
```

and group elements `g_(i,s,epsilon,k)` satisfying

```text
g_(i,s,epsilon,k) p_(i,s,epsilon,k)
 g_(i,s,epsilon,k)^(-1)=r_(i,s,epsilon,k).                (IEC3)
```

All sums are finite and every term has finite group-word support.  At least
one context assignment projection already outside the root block must remain
outside it.  The presentation may use finitely generated infinite associated
subgroups, but cannot consist solely of the finite-edge HNN transports ruled
out by `finite-edge-hnn-closures-cannot-finish-the-nonce-atlas`.

Equations `(IEC1)--(IEC3)` are the exact remaining group-theoretic interface:
they ask not only for the von Neumann trace/rank interpolation of `(WIF3)`, but
for algebraic Murray--von Neumann equivalence witnessed by group translates.

## Attempts

- **Finite character pieces:** `(FHI1)--(FHI6)` provide all transports in
  `(IEC3)`, but a finite iteration of those finite-edge HNN extensions remains
  residually finite and cannot complete the no-CE atlas.
- **Ascending HNN over the whole acyclic base:** an injective ascending HNN
  extension of the hyperlinear join-tree group is hyperlinear by
  `ascending-hnn-cannot-create-nonhyperlinearity`, so moving the whole support
  subgroup cannot be the decisive step.
- **One unconstrained stable letter:** it can conjugate `X_0` to `X_1`, but
  does not put their common value in both separator commutants and therefore
  breaks a parent attachment.
- **Live attack:** identify finitely generated proper infinite support
  subgroups carrying the relative spectral pieces in `(IEC2)`, and an
  isomorphism or finite presentation that transports those pieces while
  fixing the separator atoms.  It must not extend to an injective endomorphism
  of the whole hyperlinear base.
