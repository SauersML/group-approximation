---
rg: 2
id: reflected-corners-control-defective-quantum-variance
kind: claim
title: Defective projection expansion controls variance in a physical corner with an exterior-boundary allowance
distinct_from:
  averaged-subalgebra-energy-repairs-bistochastic-channels: That repairs a channel relative to a supplied algebra; this bounds the variance of one self-adjoint matrix in a supplied physical corner from projection expansion.
artifacts:
  - research/artifacts/reflected-corner-quantum-cheeger-bound-2026-09-08.md
---

Let `K:M_d->M_d` be unital, trace-preserving, completely positive,
and self-adjoint on normalized `L^2`. Write
`E_K(x)=tr(x*(x-K(x)))`. Let `p` be a nonzero projection and suppose
that, for constants `c>0` and `kappa>=0`, every projection `q<=p`
with `tr(q)<=tr(p)/2` satisfies

```text
E_K(q)>=c tr(q)-kappa.
```

For every self-adjoint `x=pxp`, with `M=||x||_op`, one has

```text
||x-(tr(x)/tr(p))p||_2^2
 <= (2/c^2)E_K(x)+(8M^2/c)(kappa+E_K(p)).
```

All traces, norms, energies, and the additive defect use the original
normalized trace on `M_d`. The bound is independent of both dimensions
and `tr(p)`. A second valid bound is

```text
||x-(tr(x)/tr(p))p||_2^2
 <= (2/c^2)(sqrt(E_K(x))+M sqrt(E_K(p)))^2
    +(8 kappa M^2/c).
```

An exact `M_4` example has `c=1/2`, `kappa=0`, and `E_K(x)=0`,
but corner variance `1/6`. It proves that an exterior-boundary term
cannot generally be omitted.

This establishes the variance estimate for a possible quantum
decomposition argument. It does not construct a partition into
expanding corners or prove a conditional-expectation rounding theorem.
This is a written proof, not newly Lean-verified.

DERIVATION
spectral-coarea-and-corner-reflection-prove-quantum-cheeger
