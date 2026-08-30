---
title: STW XXII audit --- intrinsic positive-dimensional selection frontier (2026-08-30)
---

## Exact reduction

For an arbitrary factorial tracial bundle over a compact metrizable base of
dimension `d`, fixed global comparison corners and a common ambient factor
are not needed by the colouring step.  It is enough that every sufficiently
small-support positive section have, locally, `m` exact weighted copies with
pairwise orthogonal ranges.  A `(d+1)`-coloured refinement activates only one
local tuple per colour.  It gives the source identity exactly and bounds the
sum of all range elements by `d+1`, independently of `m`.  Arbitrary
replication then kills every bounded trace on every norm/`2`-norm fibre gap.

For a one-dimensional base the cost is two.  This is the first conditional
positive-dimensional reduction stated entirely inside the abstract bundle:
there are no product charts, transition automorphisms, fixed factor corners,
or common ambient von Neumann algebra.

## What the intrinsic correction lemma already supplies

The weighted correction lemma in
`stw22-intrinsic-weighted-selection-proof` is uniform over all finite
factors. Starting from an exact tuple in one fibre and lifting its entries
to elements of the bundle, it proves that every nearby fibre contains an
exact tuple arbitrarily close in `L^2`. In bundle language, the exact
solution relation is lower semicontinuous. Separately, the fixed-fibre
Stiefel/unitary argument used in
`stw22-cross-stratum-selection-in-dimension-one-proof` gives path
connectedness and a principal-logarithm path with a uniform `L^2`
contraction estimate for close weighted tuples in one factor.

These are precisely the ingredients which, in a fixed ambient factor, feed
the one-dimensional Michael selection theorem.  In an arbitrary bundle,
however, they do not yet produce a continuous exact local section of the
solution relation.  The correction is existential in each nearby fibre;
its polar fill is not a section-valued operation.

## Why colouring does not fill that gap

A partition of unity can combine lifted approximate tuples, but their source
and range relations then hold only in uniform `2`-norm.  A bounded trace on
`K_x/J_x` is allowed to be discontinuous for that norm--excluding exactly
such traces is the problem being solved.  Therefore an `L^2`-small relation
defect cannot be discarded in the gap-trace estimate.  The exact source
identity in `(ILR3)` must be established before colouring.

Even convex interpolation of exact solutions is unavailable: already for a
fixed nonzero projection `p` the two exact solutions `p` and `-p` have
midpoint zero, whose source is not `p`.  In a trivial factor field Michael
selection repairs this by choosing paths inside one fixed ambient solution
space.  With varying, possibly nonisomorphic factors, the existing intrinsic
lemma gives lower semicontinuity but no theorem selecting those paths as
bundle sections.

Thus the dimension-one frontier is now exact: prove intrinsic local
replication `(ILR2)` from the lower-semicontinuous weighted solution bundle,
or construct a factorial bundle in which that local section property fails.
Either outcome requires new bundle-valued nonconvex selection input.  The
colouring and gap estimates introduce no further obstruction.

## Independent audit

An independent adversarial audit verified the global cutoff construction,
same-colour orthogonality, the exact source identities, the `d+1` range
bound, Chebyshev localization, membership in the fibre ideal, and the factor
`m` in the gap-trace estimate. It requested the compact-support wording and
the separation of lower semicontinuity from fixed-fibre path geometry made
above; with those corrections, the conditional reduction passed.
