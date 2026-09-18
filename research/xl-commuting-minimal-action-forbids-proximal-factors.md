---
rg: 2
id: xl-commuting-minimal-action-forbids-proximal-factors
kind: claim
title: A G-space with a commuting minimal action has no nontrivial proximal G-factor, so boundary-based commuting-minimal models die
distinct_from:
  stw40-trace-simplex-contains-a-nontrivial-boundary: that forces a boundary inside the trace simplex M_Gamma(X); this forbids a boundary (or any proximal flow) as a continuous factor of the underlying space X itself.
---

Let `X` be a compact space with commuting actions of a group `G` and of a
group `Gamma`, with `Gamma` acting minimally.  Let `B` be a compact `G`-flow
that is proximal (every pair `b, b'` admits a net `g_i` with
`lim g_i b = lim g_i b'`).  Then every continuous `G`-map `pi : X -> B` is
constant; its value is a `G`-fixed point.  In particular `X` has no factor
onto a nontrivial `G`-boundary, nor onto any nontrivial proximal flow.

**Corollaries (class kills for `xl-commuting-minimal-action-gives-classifiable-witness`).**

1. *Shifts over a boundary.*  Let `Y` be a compact `G`-space admitting a
   `G`-map `p : Y -> B` into a proximal flow `B` without `G`-fixed points (e.g.
   `Y = B = ` the Gromov boundary of a nonelementary hyperbolic group, or any
   extension of it).  Then no nonempty closed `G x Gamma`-invariant subset of
   `Y^Gamma` (diagonal `G`, shift `Gamma`) is `Gamma`-minimal.  So all
   Toeplitz / hierarchical block constructions of `X` over such a `Y` die at
   the minimality step, for every `Gamma`.
2. *Skew products over a boundary.*  If `X -> Y -> B` with `B` a nontrivial
   boundary (e.g. `X = K x Y` with `G` acting on `Y` and `Gamma` on `K`
   twisted by a cocycle), `Gamma` cannot act minimally.
3. *Standard amenable models.*  The usual amenable spaces of hyperbolic
   groups (their boundary), of groups acting on trees (ends), of lattices in
   semisimple groups (flag varieties `G/P`, which are boundaries) cannot be
   used, nor anything factoring onto them.

What survives: amenable `G`-spaces with no nontrivial proximal factor.  The
open named statement for the route is therefore:

> **(CMA_G)** `G` admits a compact metrizable finite-dimensional topologically
> amenable `G`-space `X` (necessarily without nontrivial proximal factors)
> carrying a commuting free minimal action of `Z` or of a locally finite group.
