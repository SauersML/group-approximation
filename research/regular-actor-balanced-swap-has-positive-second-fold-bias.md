---
rg: 2
id: regular-actor-balanced-swap-has-positive-second-fold-bias
kind: claim
title: A regular arithmetic actor and balanced swap have positive second-fold bias
distinct_from:
  sl3-swap-extension-has-defect-only-fold-square-rigidity: that asks for the fold square to converge to one in every approximate representation; this assumes the much narrower regular-actor and balanced-swap trace profile and asks only for a fixed positive real second moment.
  canonical-arithmetic-swap-fold-gram-is-arcsine: that computes zero second-fold bias in every hypothetical fully canonical microstate; this open claim would contradict that computation from only the actor character, swap balance, and presentation relations.
  canonical-sl3-double-microstates-are-uniform-two-vertex-outliers: that excludes correction to exact finite-dimensional vertex representations inside an extant canonical microstate; this asks for a direct scalar bias in precisely that two-outlier sector.
---

**OPEN CANONICAL-PROFILE TERMINAL.**  Put

```text
A=SL_3(Z[1/2]),
C=SL_3(Z),
E=<A,s | s^2=1, [s,C]=1>,
h=diag(2,1,1/2).
```

There is a constant `epsilon_*>0` with the following property.  Suppose
`rho_n` are finite-dimensional unitary assignments for a fixed finite
presentation of `E`, their presentation defects tend to zero, and after
rounding the assigned swap to a self-adjoint involution `S_n` one has

```text
tr(rho_n(a))->0                 for every 1!=a in A,
tr(S_n)->0.                                                   (RBS1)
```

Writing `H_n=rho_n(h)` and

```text
V_n=H_n S_n H_n^* S_n,
```

the desired conclusion is

```text
liminf_n Re tr(V_n^2) >= epsilon_*.                           (RBS2)
```

Equivalently, for `P_n=(I-S_n)/2` and
`Q_n=H_nP_nH_n^*`, it is enough to prove the strict profile bound

```text
limsup_n tr(Q_nP_nQ_n-(Q_nP_nQ_n)^2)
 <=1/16-epsilon_*/16.                                        (RBS3)
```

This is a strictly weaker **conclusion** than defect-only fold-square
rigidity: it asks neither that `V_n^2` approach one nor that the Gram defect
approach zero.  Its hypotheses are correspondingly narrower.  It is not
known to be an easier existence problem.  If a fully canonical microstate
sequence of `E` exists, then `(RBS1)` holds, while
`canonical-arithmetic-swap-fold-gram-is-arcsine` gives

```text
Re tr(V_n^2)->0,
tr(Q_nP_nQ_n-(Q_nP_nQ_n)^2)->1/16.
```

Thus `(RBS2)` already excludes canonical microstates and reaches the same
non-hyperlinearity endpoint.

## Attempts and exact boundary of the known methods

The near-exact sector is already controlled.  Translate an `E` assignment
to the two vertex assignments of `A*_C A` by

```text
pi_(n,0)(a)=rho_n(a),
pi_(n,1)(a)=S_n rho_n(a) S_n.
```

If either vertex is `o(1)` from an exact finite-dimensional representation,
`sl3-double-one-near-vertex-forces-joint-near-exactness` corrects the other
to the same exact representation.  Then
`sl3-arithmetic-double-near-exact-vertices-fold-projectively` gives
`|tr(V_n)|->1`.  Since a product of two self-adjoint involutions has real
trace,

```text
min_(sigma in {+1,-1}) ||V_n-sigma I||_2^2
 =2-2|tr(V_n)|,
```

and consequently `||V_n^2-I||_2->0`.  Therefore every enemy to `(RBS2)` is
in the simultaneous two-outlier sector certified by
`canonical-sl3-double-microstates-are-uniform-two-vertex-outliers`.

Nor can the scalar bias be obtained from a separated bounded-depth type
argument.  `every-fixed-dyadic-clifford-window-is-finite-fiber-folner`
shows that every fixed congruence-depth transition graph is a finite fiber
over the amenable `A_2` coweight lattice, and
`spherical-quadrature-tensors-through-clifford-folner-windows` supplies
finite models satisfying any prescribed finite spherical moment list and
bounded-depth Clifford cycles while retaining a nonfolded scalar witness.
Those models are not microstates of the full group, so this is a firewall
for that proof architecture rather than a countermodel to `(RBS2)`.

A proof must therefore use a non-tensorial same-carrier incidence between
the actor and swap, retain depth growing with conductor, or otherwise act
directly on the simultaneous two-outlier sector.
