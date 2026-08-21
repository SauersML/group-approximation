---
rg: 2
id: global-word-covariance-cannot-replace-the-capacity-gated-hecke-moment
kind: claim
title: Global packet covariance neither switches off at HALT nor controls a compressed leakage source
distinct_from:
  gauge-pair-holonomy-needs-one-source-moment: that gives a capacity-gated Hecke covariance row with automatic common Gram; this audits the stronger-looking replacement by unconditional ordinary conjugacy relators.
  isotypic-finite-edge-forces-full-commuting-selector-support: that rules out saturated logical-invariant finite edge types; this shows exactly where that no-go enters when one also asks a word to preserve a primitive packet carrier.
  context-local-fanizza-exits-do-not-control-global-leakage: that rotates a private leakage source by an outside context word; this proves the same missing commutator remains even if the uncompressed context tuple is globally conjugate to a finite packet.
---

The obvious strong replacement for `(GFM9)` is to adjoin one unitary letter
`v_c` per context and impose ordinary word relators

```text
v_c a_(c,u) v_c^(-1)=Z_u                              (GWC1)
```

for every context observable.  One might additionally make `v_c` normalize
the finite packet, or an edge subgroup selecting its primitive type, in the
hope that the selected Hecke projection is preserved.

This does not give the capacity-gated common-source cell.

## Compression identity

Let `Q` be the actual analytic leakage source `(1-C)E`.  Even if `(GWC1)`
holds approximately, compression gives the exact decomposition

```text
a_(c,u)v_cQ-v_cQZ_u
 =(a_(c,u)v_c-v_cZ_u)Q+v_c(Z_uQ-QZ_u).                (GWC2)
```

The first term is paid by the global word relator.  The second is precisely
the unknown global leakage commutator.  Preserving a larger primitive packet
corner `q` does not remove it: `Q<=q` need not reduce any `Z_u`.  Thus global
covariance closes only the **uncompressed** context row.  It does not imply
`(GFM7)` or `NCL13` for the capacity-gated source.

This is not a loose estimate.  Take `v_c=1`, `a_(c,u)=Z_u`, and any projection
`Q` not commuting with `Z_u`.  The relator error in `(GWC1)` is zero while
the compressed covariance error is exactly `||[Q,Z_u]||_2`.

## Primitive-carrier preservation returns to the finite-edge no-go

A primitive central idempotent `q_rho in C[K]` is an additive Hecke element,
not a group word.  There are two standard word-level ways to preserve it.

1. Require `v_c` to normalize `K` through a type-preserving automorphism.
   Then `v_c q_rho v_c^*=q_rho`, but the conjugated context algebra remains
   in the same finite root packet (up to one external multiplicity unitary).
   It cannot supply block-escaping holonomy.
2. Transport an edge type `sigma` into `rho` by HNN subgroup relations.  Full
   source-Gram preservation means that `Ind_H^K(sigma)` is `rho`-isotypic.
   If the logical products are fixed by the edge—as they are after gauge
   doubling—`isotypic-finite-edge-forces-full-commuting-selector-support`
   puts every compatible logical character inside `rho`.  The proper
   nonlinear predicate is lost.

A central sign is not a third option: the finite packet induction barrier
leaves every forbidden character somewhere in its marked sector.

## Exact HALT audit

The word relators `(GWC1)` are global and do not switch off when the
forbidden/capacity-gated `Q` vanishes.  An exact HALT representation extends
across `(GWC1)` only if, on the whole Hilbert space, each original context
tuple `(Z_u)` is unitarily equivalent to the restriction of a representation
of the chosen finite packet.

Countable amplification changes positive finite multiplicities into infinite
ones, but it cannot create a packet weight which is absent.  Gauge
covariantization guarantees equal multiplicity for the two share assignments

```text
(a,b) and (-a,-b),
```

yet it fixes their logical product and does not populate every missing
logical assignment.  The selected hyperoctahedral type generally contains a
fixed complete allowed support, while a particular HALT representation may
have only a proper subset of those local atoms.  Hence gauge doubling and
`H isomorphic to H directSum H` do not provide the global packet extension
required by `(GWC1)` in general.

By contrast, the capacity-gated Hecke row is vacuous when `Q=0` and only asks
for partial intertwiners on `QH`.  That is exactly why its completeness
firewall survives.

## Precise surviving distinction

Global word covariance supplies

```text
||a_(c,u)v_c-v_cZ_u||_2 <= defining relator error.      (GWC3)
```

The needed cell supplies instead

```text
||a_(c,u)V_c^*Q-V_c^*QZ_u||_2,                         (GWC4)
```

with a multi-piece block-escaping `V_c` and one common capacity-gated `Q`.
Equation `(GWC2)` proves that `(GWC4)` is strictly stronger in exactly the
matrix-only direction needed by Fanizza soundness.  The mixed Hecke moment
`(GFM8)`, or its one-root packing `(OHR2)`, cannot be replaced by unconditional
conjugacy relators without either assuming leakage reduction or destroying
the exact HALT extension.
