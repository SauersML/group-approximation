---
rg: 2
id: stw22-one-dimensional-trivial-field-trace-continuity
kind: claim
title: Trivial UHF fields over one-dimensional compact bases have only uniform traces
distinct_from:
  stw22-zero-dimensional-trivial-field-trace-continuity: that theorem uses clopen refinement and therefore stops at dimension zero; the present theorem crosses support-rank strata over arbitrary compact metrizable bases of covering dimension at most one by a finite-dimensional selection theorem.
  stw22-finite-dimensional-colouring-from-local-lifts: that theorem is conditional on local weighted corner lifting in every finite dimension; the present theorem proves the needed weighted selection unconditionally in dimension one.
  stw22-lwcl-on-fixed-support-strata: that theorem assumes a continuous fixed-trace support projection; the present theorem permits arbitrary support jumps caused by small eigenvalues.
artifacts:
  - research/artifacts/stw22-one-dimensional-cross-stratum-selection-audit-2026-08-30.md
---

Let `X` be compact and metrizable with covering dimension at most one, let
`U` be an infinite-dimensional UHF algebra with unique trace, and let `M`
be the uniform tracial completion of

```text
C(X) tensor U.
```

Then every norm/`2`-norm fibre gap `K_x/J_x` has no nonzero bounded
positive trace.  Consequently every tracial state on `M` is uniquely

```text
a |-> integral_X tau(a(t)) dmu(t)
```

for a probability measure `mu` on `X`, and is continuous for the uniform
`2`-norm.

The cross-stratum input is the following weighted selection theorem.  Let
`R` be the hyperfinite `II_1` factor, let `e in R` be a projection, and fix
`s<tau(e)`.  If `Z` is compact metrizable with `dim(Z)<=1` and

```text
a:Z -> R_+,       ||a(z)||<=1,
tau(supp(a(z)))<=s
```

is `2`-norm continuous, then there is a `2`-norm-continuous field `w` with

```text
w(z)^*w(z)=a(z),       supp(w(z)w(z)^*)<=e.             (1DS)
```

No continuity or local constancy of `supp(a(z))` is assumed.  The proof
uses lower semicontinuity of the weighted purification fibres and a
principal-logarithm contraction which makes those fibres uniformly locally
path connected even when tiny eigenvalues create new support.

For bases of dimension at least two, the same selection route requires
uniform local `k`-connectedness of the weighted fibres for `k>=1`.
Pointwise contractibility of each fixed-support Stiefel fibre does not by
itself supply that uniform cross-stratum assertion, so no higher-
dimensional conclusion is claimed here.
