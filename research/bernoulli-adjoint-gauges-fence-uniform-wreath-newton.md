---
rg: 2
id: bernoulli-adjoint-gauges-fence-uniform-wreath-newton
kind: claim
title: Bernoulli lamp gauges fence the uniform Newton upgrade from finite-image H1 vanishing
artifacts:
  - research/artifacts/coset-wreath-cartan-entropy-2026-08-22.md
distinct_from:
  finite-image-summit-wreath-relative-h1-vanishes: that proves exact first-cohomology vanishing at every finite-image representation; this identifies the two uniform analytic inputs still missing and gives an explicit exact-representation obstruction to obtaining them from the actor and Cartan alone.
  lamp-cartan-inclusion-is-not-rigid: that proves failure of relative property T from Bernoulli measures; this places the same deformation inside an adjoint Hilbert--Schmidt module and computes the resulting failure of a uniform gauge Poincare inequality.
  coset-wreath-hyperlinearity-forces-strong-one-boundedness: that is a global nonlinear microstate-covering ceiling conditional on canonical microstates existing; this concerns correction to exact finite-dimensional representations and does not infer a new entropy bound.
---

Let

```text
W_3=A rtimes Gamma,       A=direct_sum_(Gamma/Lambda) C_2.       (BAG1)
```

The theorem `finite-image-summit-wreath-relative-h1-vanishes` is a
pointwise local-rigidity theorem, not a uniform Ulam theorem.  To obtain a
dimension-independent Newton correction from it one still needs, uniformly
over all exact finite-image representations `rho`, both

```text
dist(v, tangent_to_(U(d).rho)) <= kappa^(-1)||D Rel_rho(v)||_2  (BAG2)
```

on a transverse slice, with `kappa>0`, and a uniform tubular/capture
statement saying that every sufficiently small-defect tuple enters the
slice neighbourhood where `(BAG2)` applies.  Pointwise `H^1=0` says only
that the kernel in `(BAG2)` is zero after quotienting by orbit tangents.  In
settings where the usual analytic local-rigidity theorem applies, it gives
constants depending on the individual representation stratum; pointwise
vanishing gives no positive lower bound as the finite image and `d` move.

There is an exact obstruction to deriving the missing uniform constants
from property `(T)` of `Gamma` plus the lamp Cartan.  For `0<q<=1/2`, use
the Bernoulli representation

```text
pi_q:W_3 -> U(H_q),       H_q=L^2(X,nu_q),
X=product_(Gamma/Lambda){+-1},                            (BAG3)
```

from `lamp-cartan-inclusion-is-not-rigid`, and let `xi_q=1`.  The vector is
fixed by `Gamma`.  If a lamp word has support of size `m`, then

```text
||pi_q(a)xi_q-xi_q||^2
   =2(1-(1-2q)^m) <= 4mq.                                (BAG4)
```

On the other hand `pi_q` has no invariant vector: a vector fixed by all
lamps would be supported at the trivial character, which has `nu_q`-mass
zero.

Put `rho_q=1 direct_sum pi_q`.  In the Hilbert space of Hilbert--Schmidt
operators on `C direct_sum H_q`, take the normalized skew off-diagonal
rank-two operator `T_q` determined by the rank-one map `1 |-> xi_q`.
The off-diagonal part of `rho_q(W_3)'` is the invariant-vector space of
`pi_q`, hence is zero.  Consequently

```text
dist_HS(T_q,rho_q(W_3)')=1,
max_(s in S)||Ad(rho_q(s))(T_q)-T_q||_HS -> 0             (BAG5)
```

for every fixed finite generating set `S`, by `(BAG4)`.  Thus no uniform
degree-zero adjoint Poincare/gauge inequality holds over all exact unitary
representations of `W_3`.  In particular the actor's Kazhdan constant cannot
be combined formally with Cartan spectral calculus to manufacture the
uniform full gauge control used by the standard gauge-fixed Newton proof.

This does not yet refute a uniform *finite-dimensional transverse* estimate:
the witnesses `(BAG3)` are infinite-dimensional, and `(BAG5)` consists of
almost-stabilizer directions, which are orbit directions rather than new
classes in `H^1`.  Turning them into normalized-matrix witnesses requires a
finite approximation of the Bernoulli coset action; that is exactly the
unresolved sofic/hyperlinear action interface, not a consequence of
finite-image `H^1` vanishing.

Hence the nonlinear seam has two precise possible closures and no automatic
Newton shortcut:

1. prove a uniform finite-dimensional transverse estimate together with a
   global capture theorem for canonical-character microstates; or
2. finite-dimensionalize the Bernoulli gauges (or construct another far
   family) and then count nonlinear lamp moduli modulo conjugacy.

The already-established Cartan theorem gives the global nonlinear entropy
upper bound `h(L(W_3))<=0`; it does not provide correction to finite-image
representations.  Therefore a new entropy upper bound cannot by itself close
the branch: under hyperlinearity that ceiling is already optimal.
