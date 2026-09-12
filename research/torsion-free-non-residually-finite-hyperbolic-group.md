---
rg: 2
id: torsion-free-non-residually-finite-hyperbolic-group
kind: claim
title: A torsion-free word-hyperbolic group that is not residually finite
distinct_from:
  non-residually-finite-hyperbolic-group: that allows torsion; this demands a torsion-free counterexample, and whether the two existence questions coincide is open here
  nonrf-hyperbolic-group-with-torsion-free-residual: that allows torsion outside the residual; this demands a torsion-free group, and the two are equivalent by passing to a torsion-free finite-index subgroup
---

Exhibit a torsion-free word-hyperbolic group that is not residually finite.

It settles `non-residually-finite-hyperbolic-group`.  It is equivalent to
`nonrf-hyperbolic-group-with-torsion-free-residual`.  Whether it follows from
an arbitrary counterexample is **open** here: every equivalent shape proved in
this region (invisible torsion, the Kazhdan shape, the non-MF shape) may carry
torsion.

## Attempts

- **Torsion-free finite-index subgroup.**  Works exactly for counterexamples
  whose residual is torsion-free (route
  `torsion-free-nonrf-from-torsion-free-residual`).
- **Rips construction over the Kazhdan shape.**  Let `1 -> N -> T -> Q -> 1`
  with `T` torsion-free hyperbolic (Rips' small-cancellation total group) and
  `Q` without nontrivial finite quotients.  For every homomorphism
  `phi : T -> F` to a finite group, `F/phi(N)` is a finite quotient of `Q`,
  hence trivial, so `phi(N) = F`.  Every finite quotient of `T` is detected on
  the kernel, and the invisibility of `Q` does not lift to `T`.  Dead as a
  general transfer.
- **Olshanskii common quotients.**  They preserve conjugacy classes of
  finite-order elements, so they cannot remove torsion from the Kazhdan shape.
