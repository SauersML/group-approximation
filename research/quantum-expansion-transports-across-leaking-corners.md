---
rg: 2
id: quantum-expansion-transports-across-leaking-corners
kind: claim
title: Projection expansion transfers across physical corners with a trace leakage allowance
distinct_from:
  reflected-corners-control-defective-quantum-variance: That starts with expansion inside the actual corner; this transports expansion from a different tested corner, controlling the loss by physical trace leakage.
  low-energy-povms-yield-flexible-projection-cuts: That supplies overlapping cuts and word repair; this gives a sufficient expansion test for those cuts and bounds the aggregate cost of leaving the original tested corner.
artifacts:
  - research/artifacts/quantum-corner-expansion-transport-2026-09-08.md
---

Let `K:M_d->M_d` be self-adjoint, bistochastic and UCP, with
normalized trace and energy `E(x)=tr(x*(x-K(x)))`. Suppose every
projection `q<=p` with `tr(q)<=theta` satisfies

```text
E(q)>=c tr(q)-kappa,       c>0, kappa>=0.
```

For any nonzero projection `r` with `tr(r)/2<=theta`, put
`ell=tr(r(1-p))`. Every projection `q<=r` of at most half its
trace satisfies

```text
E(q)>=(c/2)tr(q)-kappa/2-(c/2+4)ell.
```

Consequently, every self-adjoint `x=rxr`, with `M=||x||_op`, obeys

```text
||x-(tr(x)/tr(r))r||_2^2
 <=(8/c^2)E(x)+(8M^2/c)kappa
   +(8+64/c)M^2 ell+(16M^2/c)E(r).
```

For a family with `sum_i r_i<=C I`, leakage from one common tested
corner has total at most `C tr(1-p)`. Thus leaving a large retained
corner can be paid once across all outcomes.

For ordered orthogonal seeds `p_0,...,p_m` and spectral cuts
`r_i<=3K(p_i)`, leakage from the changing remaining corners instead
has total at most `3 beta/2`, where `beta=sum_i E(p_i)`. This is an
exact symmetric-flow bound; small local relative seed costs alone
do not make its ratio to the expansion threshold vanish.

The artifact also proves `E(sum_i w_i q_i)<=4C sum_i w_i E(q_i)`
for projections with nonnegative weights and `sum_i w_i q_i<=C I`, and gives exact
examples showing why the leakage allowance cannot be omitted or
replaced by a function of the idempotence defect alone.

This transports a supplied expansion test. It does not select the
seeds, prove a quantum expander decomposition, or settle nonhyperlinearity.

DERIVATION
principal-angle-transport-and-projection-frame-energy
