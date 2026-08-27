---
rg: 2
id: diffuse-pin-centralizer-has-zero-quadratic-covering
kind: claim
title: The unitary centralizer of a diffuse microstate pin has zero quadratic covering entropy
artifacts:
  - research/artifacts/anchored-orbit-covering-2026-08-22.md
distinct_from:
  finite-congruence-wreath-lamp-torsors-are-subquadratic-gauge: that counts global unitary-equivalence classes of exact wreath representations; this is the analytic finite-level estimate showing that fixing a diffuse Hayes pin leaves only subquadratic conjugation freedom inside each class.
  coset-wreath-microstates-carry-excess-entropy: that asks for a positive quadratic lower bound for full wreath microstate fibers; this supplies the matching zero upper bound for every fiber supported on subexponentially many exact unitary orbits.
---

Let `a` be a diffuse self-adjoint element of a tracial von Neumann algebra and
let `A_d in M_d(C)_sa` be a uniformly bounded microstate sequence for `a`.
For every fixed `epsilon>0`,

```text
limsup_(d->infinity) d^(-2) log K_epsilon(
  {U in U(d) : U A_d = A_d U}, ||.||_infinity) = 0.       (DPC1)
```

Consequently, for every finite index set `F`, every uniformly
operator-norm-bounded tuple `X_d in M_d(C)_sa^F`, and every fixed
`epsilon>0`,

```text
limsup_(d->infinity) d^(-2) log K_epsilon(
  {U* X_d U : U A_d = A_d U}, ||.||_2) = 0.              (DPC2)
```

More generally, if `Omega_d` is contained in a union of `N_d` such pinned
centralizer orbits, with `log N_d=o(d^2)`, then

```text
limsup_(d->infinity) d^(-2) log K_epsilon(Omega_d,||.||_2)=0. (DPC3)
```

The constants are uniform in the reference tuples once their operator-norm
cutoff and the finite coordinate set are fixed.
