---
rg: 2
id: anchored-exact-wreath-packets-have-zero-entropy
kind: claim
title: Exact finite wreath packets remain entropy-null after fixing a diffuse lamp pin
artifacts:
  - research/artifacts/anchored-orbit-covering-2026-08-22.md
distinct_from:
  finite-congruence-wreath-lamp-torsors-are-subquadratic-gauge: that removes the apparent lamp torsor after quotienting by global conjugacy; this proves the same no-moduli conclusion directly in Hayes' anchored microstate spaces, where one diffuse lamp coordinate is fixed exactly.
  finite-wreath-relative-tangent-moduli-vanish: that is an infinitesimal cohomological statement near one finite packet; this is a global covering-number statement for all exact packet classes at fixed matrix size.
---

Let `H_d=A_d rtimes Q_d` be any sequence of finite wreath packets and let
`Omega_d` be a uniformly bounded family of exact `d`-dimensional
representations of `H_d`, written as a fixed finite self-adjoint generating
tuple.  Suppose the number `N_d` of unitary-equivalence classes represented
in `Omega_d` satisfies

```text
log N_d=o(d^2).                                           (AEW1)
```

Choose, inside the growing finite lamp algebras, self-adjoint observables
`D_d` whose moments converge to a diffuse law, and restrict to the anchored
fiber in which this coordinate is exactly the prescribed matrix `D_d`.
Then for every fixed `epsilon>0`,

```text
limsup_(d->infinity) d^(-2) log K_epsilon(
  Omega_d |_(lamp pin = D_d), ||.||_2) = 0.              (AEW2)
```

In particular, the exact regular-character congruence-wreath packets have
one unitary-equivalence class, and arbitrary exact packet representations
have at most `(d+1)^|Irr(H_d)|` classes.  Whenever that class count is
subquadratic (including the regular packets used in the summit-wreath
construction), exact packet models contribute zero anchored 1-bounded
entropy.  A positive entropy witness must therefore use approximate models
that stay a fixed distance from every subquadratic union of exact finite
packet orbits.
