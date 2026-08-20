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
  amenable-edge-hnn-preserves-hyperlinearity: that excludes every amenable associated subgroup by a general permanence theorem; this leaves a nonamenable proper infinite edge or a non-Bass--Serre mechanism.
  finite-free-phase-product-embedding-has-an-injective-coordinate: that proves every injective map into finitely many commuting free-phase copies has a faithful coordinate; this leaves only nonextendable partial-graph coupling or a non-product support geometry.
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
- **Amenable proper infinite edge:**
  `amenable-edge-hnn-preserves-hyperlinearity` proves that every HNN extension
  of a hyperlinear base over an amenable associated subgroup is hyperlinear.
  Thus replacing finite character pieces by cyclic, locally finite, or other
  amenable infinite packets cannot close the chord either.
- **Symmetric proper infinite edge:**
  `free-phase-context-support-is-a-proper-free-factor` identifies the exact
  rank-`D-1` free factor carrying one escaped block.  Identifying two such
  factors while fixing the previous support gives the path-RAAG height kernel
  of `symmetric-free-support-hnn-remains-hyperlinear`, so the first natural
  proper infinite HNN is still hyperlinear.
- **Diagonal depth-doubling edge:**
  `diagonal-hnn-exactly-advances-free-phase-depth` maps every coefficient
  `a_i a_j^(-1)` to the product of two commuting copies, so it transports the
  escaped block exactly and asymmetrically.  Reversing its stable letter gives
  the Formanek--Procesi group.  By
  `formanek-procesi-diagonal-hnn-is-residually-finite`, this candidate is also
  residually finite and hyperlinear.
- **Distorted diagonal edge:** replacing the second copy by any injective
  endomorphism of the free support still fails.
  `graph-endomorphism-phase-hnn-embeds-formanek-procesi` embeds the resulting
  graph HNN in the same residually finite Formanek--Procesi group by an exact
  Britton argument.
- **Several individually lossy phase coordinates:** impossible at finite
  depth.  `finite-free-phase-product-embedding-has-an-injective-coordinate`
  proves that an injective map of a free support group into a finite product
  of free groups must be injective in one coordinate.  Thus every finite-layer
  transport is a graph over one embedded free subgroup; the remaining live
  case is precisely when the other coordinate maps on that subgroup do not
  extend to endomorphisms of the ambient free factor.
- **One unconstrained stable letter:** it can conjugate `X_0` to `X_1`, but
  does not put their common value in both separator commutants and therefore
  breaks a parent attachment.
- **Live attack:** couple finitely generated nonamenable proper infinite
  support subgroups asymmetrically so that `(IEC2)--(IEC3)` hold while the height kernel is not
  the path graph product above or a graph-endomorphism subgroup of a
  Formanek--Procesi HNN.  The transport must fix the separator atoms, must not
  extend to an injective endomorphism of the whole hyperlinear base, and must
  use nonextendable partial-graph data on a proper embedded free subgroup (or
  leave finite-product free-phase geometry entirely) so that it carries
  genuine cycle holonomy rather than merely renaming or duplicating fresh
  free factors.
