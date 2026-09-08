---
rg: 2
id: iwahori-quadratic-step-from-neutral-directions
kind: route
title: Run the second-order step on a flat neutral direction and count the padding
target: iwahori-uniform-quadratic-repair-step
requires:
  - iwahori-admits-neutral-quadratic-directions
  - second-order-step-beats-a-blocked-linearization
  - word-taylor-remainder-has-a-fourth-moment-bound
artifacts:
  - research/artifacts/pde-transfer-quadratic-repair-2026-09-08.md
---

Let `pi` have defect `e <= eps`.  The first prerequisite supplies the padding
`r <= B e d`, which is clause three of `(QS1)`, and on the padded pair a
`kappa`-flat neutral direction `xi` with `||xi||_(2,d) <= C sqrt e` and the
blocked-component bound of `(NQ1)`, together with a `kappa`-flat linear
correction `eta` of size `O(e)`.

**The norms match.**  Apply the second prerequisite with `E` the tangent space
in normalized Hilbert-Schmidt norm and `Y` the defect space in the same norm.
Its proof needs `D^2F` only at `(xi, xi)`, `(xi, eta)`, `(eta, eta)` and
`D^3F` only at `(v, v, v)` with `v = xi + eta`.  Every entry of `D^2F` is a
product of generator matrices with two tangent factors inserted and every entry
of `D^3F` has three, so the third prerequisite's Hoelder estimate gives

```text
||D^2F[X, Y]||_(2,d) <= L^2 ||X||_(4,d) ||Y||_(4,d) <= L^2 kappa^2 ||X||_2 ||Y||_2,
||D^3F[X, X, X]||_(2,d) <= L^3 ||X||_(6,d)^3 <= L^3 kappa^3 ||X||_2^3,
```

on the flat cone, `L` a bound for the lengths of the defining words.  So the
constants `M_2 = L^2 kappa^2` and `M_3 = L^3 kappa^3` are dimension-free, which
is what the second prerequisite requires and what a naive appeal to a bound on
the full differentials would not have: by
`normalized-hs-taylor-remainder-is-not-dimension-free` no such bound exists.
Flatness of `v = xi + eta` follows from flatness of the summands once `e` is
small enough that `||eta||_2 <= ||xi||_2 / 2`.

**Output.**  The second prerequisite then gives `pi^+ = pi + xi + eta` with
`def(pi^+) <= A e^(3/2)` and `||xi + eta||_(2,d) = O(sqrt e)`, the first two
clauses of `(QS1)`; the movement bound transfers to the zero-padding metric
because the padded and unpadded tuples differ only by the adjoined exact block,
which the metric charges at most the padding ratio.  The constants depend only
on `C, kappa, L` and the right-inverse bound, all of which the first
prerequisite asserts uniformly, so they are the same at `pi^+` and the step may
be iterated.

**What this route does not do.**  It does not produce `xi`; the whole content
sits in its first prerequisite, and
`iwahori-second-order-repair-space-is-empty` already proves that prerequisite
fails at compatible pairs and near them.
