---
rg: 2
id: leavitt-kernel-packet-has-a-finite-coefficient-rank-gap
kind: claim
title: Three Leavitt kernel words have normalized rank gap at least one fifteenth in literal finite coefficient matrices
distinct_from:
  leavitt-24k-kernel-packet-excludes-scalar-field-models: that excludes nonzero scalar assignments; this bounds every assignment of finite matrices over a characteristic-two field, including singular coefficients.
  leavitt-24k-feasibility-has-a-uniform-gap: that asks for a normalized-HS gap over arbitrary complex relative unitaries; this is a rank-metric statement in a restricted coefficient realization.
artifacts:
  - research/artifacts/leavitt-finite-coefficient-rank-gap-2026-09-08.md
---

Let `K` be any field of characteristic two, `d>=1`, and
`s,t,v in M_d(K)`. Evaluate the three words `r_*`, `R_v`, `R_0`
of `leavitt-24k-kernel-packet-excludes-scalar-field-models` using
the coordinate three-cycle and `b_i=x_12(s),x_12(t),x_12(v)`
in `GL_(3d)(K)`. Set `rho(W)=rank(W-I)/(3d)`. Then

```text
rho(R_0)+rho(R_v)+3 rho(r_*) >= 1/3,
max(rho(r_*),rho(R_v),rho(R_0)) >= 1/15.
```

No invertibility, independence, or regularity assumption on `s,t,v`
is needed. Over any nonzero directly finite unital ring of
characteristic two, the same three words have no simultaneous exact
solution in this literal three-by-three coefficient realization.

This is not a normalized-HS lower bound for the complex `24k`
problem. Arbitrary unitary values of these words do not come equipped
with the coefficient ring and block positions used in this proof.
