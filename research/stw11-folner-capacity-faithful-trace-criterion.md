---
rg: 2
id: stw11-folner-capacity-faithful-trace-criterion
kind: claim
title: Positive maximal Følner averages exactly characterize faithful invariant measures
distinct_from:
  stw12-faithful-invariant-trace-af-criterion: that converts a faithful invariant trace into a simple-AF embedding for one automorphism; this gives an intrinsic orbit-average criterion for existence of the faithful invariant measure and applies to higher-rank actions.
  stw11-clopen-exhaustion-glues-qd: that handles some actions without a faithful invariant measure by projectional support gluing; this instead detects exactly when one faithful invariant measure exists and needs no clopen subsets.
  stw11-lattice-coupled-cyclic-products-are-af-embeddable: that extracts AF embeddings from a product-of-cyclic presentation even without a faithful measure; this applies to arbitrary higher-rank actions satisfying the Følner-capacity condition.
artifacts:
  - research/artifacts/stw11-folner-capacity-audit-2026-08-30.md
---

Let `alpha:Z^d -> Homeo(X)` act on a nonempty compact metrisable space,
and put

```text
F_N=[-N,N]^d intersect Z^d,
A_N(f)=|F_N|^(-1) sum_(g in F_N) alpha_g(f).
```

For every `f in C(X)_+`, the maximal Følner averages satisfy the exact
variational formula

```text
lim_(N->infinity) ||A_N(f)||
  =max_{nu invariant probability} nu(f).                   (FC0)
```

Consequently, the following are equivalent.

1. `X` carries a faithful `alpha`-invariant Borel probability measure.
2. Every nonzero `f in C(X)_+` has positive maximal Følner capacity:

   ```text
   lim_(N->infinity) ||A_N(f)|| > 0.                       (FC1)
   ```

When these conditions hold, the full/reduced crossed product
`C(X) rtimes_alpha Z^d` embeds into a unital simple AF algebra.  Thus it is
quasidiagonal and stably finite.

In particular, `(FC1)` holds whenever the union of the minimal closed
invariant subsets is dense in `X` (equivalently, whenever minimal points are
dense).  Hence every `Z^d`-action with dense minimal points has an
AF-embeddable crossed product.  No minimality, finite orbit decomposition,
product-of-cyclic presentation, zero-dimensionality, or compact-open support
filtration is required.
