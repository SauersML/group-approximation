---
rg: 2
id: cyclic-carrier-energy-stability
kind: claim
title: Preserve one strict finite-dimensional cyclic-energy ceiling under matrix ultraproduct limits
artifacts:
  - research/artifacts/cyclic-carrier-energy-and-outlier-audit-2026-08-21.md
distinct_from:
  matrix-only-cyclic-carrier-invariance: that forces approximate cyclic energy to zero; this permits nonzero exact finite-dimensional energy and asks only that one scalar supremum not jump above its exact ceiling.
  leavitt-steinberg-hs-stable: that asks to perturb whole approximate representations to exact ones; this asks upper semicontinuity of one fixed trace-polynomial energy and no operator correction.
  non-ce-bcs-has-robust-approximate-energy-gap: that is a lower gap for additive BCS relations; this is an upper ceiling for a cyclic commutator energy in approximate group representations.
---

Construct finitely presented data `G=<X|R>`, `H=<S><=G`, an infinite-order
word `w`, and a nonconstant trigonometric polynomial `f`. Define

```text
E(U)=sum_(s in S)||[U(s),f(U(w))]||_2^2,
beta_fd=sup_(pi exact finite-dimensional) E(pi),
beta_app(delta)=sup_(d,U:def_R(U)<=delta) E(U),
E_reg=E(lambda_G).
```

Require

```text
beta_fd<E_reg,
limsup_(delta->0) beta_app(delta)<=beta_fd.              (CES)
```

Equivalently, every matrix-ultraproduct homomorphism has this one scalar
energy at most the exact finite-dimensional ceiling. No closeness to an
exact representation is required.

More precisely, put

```text
a=sum_(s in S)[s,f(w)]^*[s,f(w)] in C[G]_+.
```

Let `T_CE` be the traces of the form `tr_omega circ rho`, where `rho` is a
unital star-homomorphism from `C*(G)` to a tracial matrix ultraproduct, and
let `T_fd` be the weak-star closed convex hull of normalized
finite-dimensional representation traces. (The first set is weak-star closed
by the usual diagonal microstate argument.) Then

```text
lim_(delta->0) beta_app(delta)=sup_(tau in T_CE)tau(a),
beta_fd                         =sup_(tau in T_fd)tau(a). (CES*)
```

For the first equality, near-maximizers at defects `1/n` define an
ultraproduct representation and attain the decreasing limit. Conversely,
coordinate lifts of any ultraproduct representation have relator defects
tending to zero and energy tending to `tau(a)` along the ultrafilter. Thus
`(CES)` is exactly equality of one support functional on the CE and
finite-dimensional trace sets. Approximation of all finite joint
conjugacy-orbit moments occurring in `a` is a stronger sufficient condition;
`(CES)` itself controls only the single scalar `tau(a)`.

Equivalently, for every `epsilon>0` there is `delta>0` such that every
`delta`-representation `U` admits some exact finite-dimensional
representation `pi` (in an unrelated dimension) with

```text
E(U)<=E(pi)+epsilon.
```

This equivalence concerns only the scalar functional `E`: no matrices from
`U` are perturbed or compared with matrices from `pi`. It makes explicit why
`(CES)` is strictly weaker than full HS stability.

## Attempts

- `shifted-infinite-heisenberg-wreath-exact-mci-is-hyperlinear` realizes the
  strict exact gap with `beta_fd=0`, but its hyperlinear models violate
  `(CES)`. Exact finite-dimensional classification alone is therefore
  insufficient.
- The same firewall survives when the acting property-`(T)` subgroup is
  character-rigid. Character rigidity of `H` does not control the joint
  `H`--carrier moments in `C*(G)`.
- Semiprojectivity of `C*(w)` and ordinary finite-operator-system ucp lifting
  do not help: CE traces already have coordinate ucp lifts. What is needed is
  representation-valued approximation of the specific orbit moments in `a`.
- The property is genuinely weaker than full HS stability. If a group `G_0`
  has `(CES)` for `a` and `L` is any non-HS-stable group, then `G_0 x L` still
  has `(CES)` for the pullback of `a` (restrict approximate models to `G_0`,
  and extend exact `G_0` models trivially across `L`), while the bad models of
  `L` extend trivially across `G_0`.
- Residually finite candidates are impossible: a finite quotient injective
  on the finite supports defining `E` has quotient-regular energy exactly
  `E_reg`.
- Full HS stability would prove `(CES)` but is far stronger than needed and
  is unavailable for infinite hyperlinear property-`(T)` groups. The live
  target is one-polynomial upper semicontinuity, potentially from a
  finite-dimensional multiplicity or holonomy invariant.
