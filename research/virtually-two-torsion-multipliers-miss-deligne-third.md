---
rg: 2
id: virtually-two-torsion-multipliers-miss-deligne-third
kind: claim
title: Multipliers whose square dies on a finite-index subgroup never reach the Deligne third, even asymptotically
distinct_from:
  sp4-metaplectic-class-pointwise-coboundary-limit: that proves pointwise closedness of scalar coboundaries; this uses it together with Deligne invisibility to exclude a whole class of asymptotic-model constructions from the triple-cover sector.
  deligne-triple-cover-fd-central-invisibility: that is about exact finite-dimensional representations of E_3; this is about multiplier cocycles of operator-norm asymptotic models that only become 2-torsion after restriction.
  sp4-schur-kernels-miss-every-deligne-multiplier: that kills Schur-kernel constructions by a kernel computation; this names the invariant (restricted multiplier class on a finite-index stabilizer) that kills every stabilizer-evaluated symbol calculus.
---

Let `Gamma = Sp_4(Z)`, and let `E_3` be Deligne's triple cover with a
set-theoretic section `s` and `Z/3`-valued cocycle `b`,
`s(g)s(h) = z^(b(g,h)) s(gh)`.  Put

```text
c_j(g,h) = exp(2 pi i j b(g,h)/3),   j = 1, 2.            (VT0)
```

Call `omega in Z^2(Gamma,T)` **virtually 2-torsion** if there is a
finite-index subgroup `Gamma' <= Gamma` such that `omega^2|Gamma'` is a
coboundary.

**(VT1) Exact form.**  No virtually 2-torsion cocycle is cohomologous to
`c_1` or `c_2`.

**(VT2) Asymptotic form.**  Let `rho_n : Gamma -> U(d_n)` satisfy
`||rho_n(g)rho_n(h) - omega_n(g,h) rho_n(gh)|| -> 0` for all `g,h`, where
`omega_n -> omega` pointwise and `omega` is virtually 2-torsion.  Then for no
choice of scalar gauges `mu_n : Gamma -> T` is `mu_n rho_n` an operator-norm
asymptotic `c_1`- or `c_2`-projective model.

So an attempt to show `1/3 in P_op` (equivalently that `E_3` is MF) cannot
succeed through any construction whose leading multiplier is virtually
2-torsion.  The invariant is the class of the leading multiplier restricted
to a finite-index subgroup.  Every member of the class fails at the step
"the multiplier squared is trivial on `Gamma'`".  There it would induce a
`[Gamma:Gamma']`-dimensional exact `c_2`-representation, which Deligne
invisibility forbids.

## Attempts

- **Main application (conditional; recorded in the Attempts of
  `deligne-triple-cover-is-not-mf`).**  Take Toeplitz or Zelditch quantized
  contact transformations of a quantizable symplectic `Gamma`-action on a
  compact integral symplectic manifold that has a finite orbit.  By the
  symbol calculus at the fixed point of the stabilizer, their leading
  multipliers are virtually 2-torsion.  That structural input is a
  citation-level hypothesis, not proved here.
