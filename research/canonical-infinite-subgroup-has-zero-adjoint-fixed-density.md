---
rg: 2
id: canonical-infinite-subgroup-has-zero-adjoint-fixed-density
kind: claim
title: Canonical microstates give every infinite subgroup zero pointwise-fixed adjoint density
distinct_from:
  commutant-density-trace-blind: that computes an iterated Kazhdan-average commutant density for property-(T) groups; this is a direct finite-averaging estimate for every infinite subgroup and every approximation-dependent fixed projection.
  fixed-finite-quotient-adjoint-walls-are-canonical-trace-null: that treats sectors on which the kernel of one fixed finite quotient acts trivially; this needs no quotient and applies to the full infinite subgroup.
  tracial-superoperator-self-copy-has-no-macroscopic-excess: that compares parent and child fixed projections for arbitrary asymptotic representations; this uses canonical trace and proves that either fixed projection already has trace zero when the subgroup is infinite.
---

Let `H<=G` be infinite and let

```text
u_n:G->U(d_n)
```

be normalized-Hilbert--Schmidt asymptotic representations converging to the
canonical group trace.  Put

```text
S_n(h)=u_n(h) tensor conjugate(u_n(h)) in U(d_n^2).
```

If orthogonal projections `E_n in M_(d_n^2)` satisfy, for every fixed
`h in H`,

```text
||(S_n(h)-1)E_n||_(2,d_n^2)->0,                       (CIA1)
```

then

```text
tr_(d_n^2)(E_n)->0.                                   (CIA2)
```

Thus canonical microstates cannot contain a positive-density adjoint sector
whose range is pointwise fixed by an infinite subgroup.  The conclusion is
about fixed ranges, not invariant ranges: a positive-rank left ideal may be
preserved by the adjoint action while its pointwise-fixed part still has
vanishing density.

