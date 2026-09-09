---
rg: 2
id: hermitian-dilation-and-conic-duality-control-residuals
kind: route
title: Use square-root Lipschitz control and least-squares duality to sharpen a soft packing residual
target: soft-projection-cones-have-low-energy-residuals
requires: []
artifacts:
  - research/artifacts/soft-projection-cone-residual-energy-2026-09-08.md
---

The absolute-value function is 1-Lipschitz in Hilbert--Schmidt
norm on self-adjoint matrices. Apply it to Hermitian dilations
of the row matrix `(sqrt(w_i)q_i)_i` and its simultaneous
unitary conjugate. The upper-left corner gives

```text
||[U,sqrt(S)]||_2^2<=2sum_i w_i||[U,q_i]||_2^2.
```

Differentiate at `U=exp(itH)`, and sum over a self-adjoint
Kraus representation of the channel. This proves the first
energy bound with no operator bound on `S`. The scalar map
`z -> (1-z^2)_+` is 2-Lipschitz on the nonnegative axis,
which proves the residual estimate.

Finite-dimensional closed-cone minimization is coercive and
strictly convex. Scaling the minimizing sum proves
`tau(S^2)=tau(S)`, and one-sided variation along each allowed
projection proves `tau((I-S)q)<=0`. The soft-sum energy
estimate passes to the closed cone by continuity.

With `X=I-S` and `R=X_+`, energy Cauchy--Schwarz gives

```text
tau(X K(R))>=tau(R^2)-sqrt(E_K(X)E_K(R))
           >=Delta^2-4sqrt(h Delta).
```

Since `R` is a contraction, the actual mixed-norm defect
bounds `E_K(K(R))` by `delta`. Full spectral coarea then
bounds the integral of the energies of its threshold
projections by `sqrt(delta/2)`. Removing the thresholds
with excessively large energy leaves a threshold with
the positive dual gain and constants in the claim.

The artifact gives every step directly and explains why
the projection pool must retain its additional admissibility
requirements. It does not infer expansion of a spectral cut
merely from that cut's low energy.

For finite rational weights `w_i=k_i/M`, take `k_i` copies of
each corner and scale their inclusion maps by `1/sqrt(M)`.
The resulting row map satisfies `JJ*=S`. On block-diagonal
matrices its squared Hilbert--Schmidt norm is exactly the
amplified trace divided by `Md`, even though the physical
corners need not be orthogonal. Corner polar completion and
word telescoping therefore give (4) of the claim. The only
source-error estimate required is
`tau(A*A S)<=||A||_2^2+2||A||_2||S-I||_2` for `A=U_w-I`.
This turns weighted cone coverage into a genuine flexible
model construction; it needs neither an operator bound on
`S` nor purity of the individual weighted projections.
Finite sums and rational weights approximate arbitrary cone
elements, with all displayed errors continuous. The missing
step remains coverage by a suitably expanding projection pool.
