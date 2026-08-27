---
rg: 2
id: koopman-weighted-energy-is-linearized-gauge-distance
kind: claim
title: Weighted Koopman inverse energy is exactly linearized gauge distance
distinct_from:
  iwahori-cubics-control-aggregate-weighted-bs-orbit-energy: that asks the full Iwahori relators to bound this quantity by presentation defect; this identifies the quantity itself, without supplying that nonlinear error bound.
  bounded-cycle-coboundary-inverse: that bounds the inverse when cycle length is bounded; this is an exact identity at every cycle length and permits the inverse norm to diverge.
  movable-weyl-gauge-refutes-iwahori-cubic-low-mode-gain: that constructs a nonlinear correcting gauge saturating the scale; this proves the general linearized variational identity explaining the saturation.
---

Let `H` be a finite-dimensional Hilbert space, let `psi` be unitary on
`H`, put `D=1-psi`, and let `b` be orthogonal to `ker(D)`.  If `P_lambda`
denotes the spectral projection of `psi`, then

```text
inf { ||a||^2 : a perpendicular ker(D), D a=b }
 = sum_(lambda != 1) ||P_lambda b||^2/|1-lambda|^2.     (KGD1)
```

For the dyadic bands

```text
P_t=1_(t/2<|1-psi|<=t),
E_dyad(b)=sum_t t^(-2)||P_t b||^2,
```

the same identity gives

```text
(1/4)||D^dagger b||^2 <= E_dyad(b) <= ||D^dagger b||^2, (KGD2)
```

where `D^dagger` is the minimum-norm inverse on `ker(D)^perp`.

In the Iwahori application, `H=L^2(Z,tau)` for the base commutant,
`psi=Ad(h)`, and the infinitesimal action of a correcting gauge
`c(t)=exp(t a)` on the Weyl residual is

```text
d/dt|_(t=0) [c(t) psi(c(t))^(-1)] = D a               (KGD3)
```

up to the harmless sign/orientation convention.  Consequently the left
side of `iwahori-cubics-control-aggregate-weighted-bs-orbit-energy` is,
within the factor four in `(KGD2)`, exactly the squared distance of the
centered Weyl residual from zero measured in the linearized correcting-
gauge metric.

Thus the corrected cubic target is not a Fourier-decay assertion.  It is
the nonlinear error bound

```text
minimum correcting-gauge distance <= C * full-presentation defect, (KGD4)
```

after the fixed holonomy component is removed.  The long-cycle first mode
does not contradict `(KGD4)`; it says only that residual HS norm and gauge
distance are not uniformly equivalent.  Any proof of `(KGD4)` must use the
two cubic rows to charge the correcting gauge modulo exact gauge/tangent
directions.  Bare BS dynamics, trace moments, lacunarity, or Parseval cannot
do this because none of them sees that quotient metric.

At an exact compatible congruence point the differential form of `(KGD4)`
is precisely the corresponding restricted Fox-Jacobian gap supplied by
`iwahori-uniform-infinitesimal-rigidity`.  The unresolved content is a
dimension-free nonlinear error bound outside an operator-norm tube; the
normalized-HS Taylor obstruction prevents obtaining it formally from the
Jacobian gap alone.

