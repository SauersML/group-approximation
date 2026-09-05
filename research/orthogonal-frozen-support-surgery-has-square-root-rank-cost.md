---
rg: 2
id: orthogonal-frozen-support-surgery-has-square-root-rank-cost
kind: claim
title: Frozen orthogonal support surgeries cost the square root of their cumulative rank
artifacts:
  - research/artifacts/flexible-curvature-surgery-audit-2026-09-05.md
distinct_from:
  two-kazhdan-correction-concentrates-normalized-hs-curvature: that supplies small curvature supports with no invariance; this assumes exact reducing supports and proves convergence from a cumulative correction and rank budget.
  moving-subgroup-schreier-correction-has-no-index-loss: that constructs an exact representation from exact subgroup holonomy; this obtains an exact representation by an independently supplied infinite surgery schedule, without claiming such a schedule exists for a lattice.
---

Let `G=<S|R>` be finitely presented. Fix a finite dimension `d`; every
2-norm and trace below is normalized by this **original** dimension,
including after some subspaces have been frozen. Suppose unitary generator
tuples `U^k,W^k:S->U(d)` and projections `P_k`, for `k>=0`, satisfy:

1. The `P_k` are pairwise orthogonal, and with
   `F_k=sum_(i<k)P_i`, both `U^k_s` and `W^k_s` restrict to the identity
   on `F_k C^d` for every generator. In particular they preserve that
   subspace and its orthogonal complement.
2. `P_k<=I-F_k` commutes exactly with every `W^k_s`.
3. `U^(k+1)_s=W^k_s(I-P_k)+P_k`.
4. `max_s||W^k_s-U^k_s||_2<=a_k`, with
   `sum_k a_k<infinity`, and `sum_k tr(P_k)<=eta`.
5. `max_r||U^k(r)-I||_2->0` as `k->infinity`.

Then `U^k_s` converges to the generators of an exact representation
`rho:G->U(d)`, and

```text
max_s||rho(s)-U^0_s||_2 <= sum_k a_k+2 sqrt(eta).          (OFS1)
```

Zero projections are allowed. In fixed finite dimension there are at
most `d` nonzero cuts, but smooth corrections may continue indefinitely.
The vanishing-relator and summability assumptions are still needed after
the last nonzero cut. A finite schedule gives the same bound with finite
sums if its last tuple has zero relator defect; a nonzero terminal defect
does not give an exact representation.

The conclusion is uniform in `d` if its two budgets are uniform. In
particular, for a sequence of such schedules, `sum_k a_(j,k)->0` and
`sum_k tr_(d_j)(P_(j,k))->0` give exact representations asymptotic to the
input tuples, in the same dimensions.

There is a useful conditional stability criterion. Suppose a repair
method, uniformly in dimension and preserving every already frozen block,
takes a tuple of defining defect at most delta to an intermediate tuple
at generator distance at most `C delta`, supplies a new exact reducing
support of relative rank at most `m(delta)`, and after trivial replacement
has defining defect at most `delta/2`. All of these quantitative statements
use the original dimension. Let `m` be nondecreasing. If

```text
D_m(delta)=sum_(k>=0) m(2^(-k)delta) < infinity,
D_m(delta)->0 as delta->0,                              (OFS2)
```

then the group has same-dimension normalized-HS stability, with modulus

```text
max_s||rho(s)-U_s||_2 <= 2C delta+2 sqrt(D_m(delta)).       (OFS3)
```

If a method is instead stated in the dimension of the current active
block, the corresponding original-dimension accounting must be checked.
It is sufficient to use `D_m(sqrt(2)delta)<1/2` in `(OFS3)` in place of
`D_m(delta)`; then all active blocks retain more than half the original
dimension, and the normalization conversion is valid throughout. The
proof spells out this bootstrap.

This statement neither supplies the repair method nor obtains exact
reducing supports from almost invariant ones. No subgroup holonomy,
`SL_5(Z)` stability, relative-commutant collapse, or non-hyperlinear group
is asserted without those missing hypotheses.

DERIVATION
orthogonal-frozen-support-surgery-proof
