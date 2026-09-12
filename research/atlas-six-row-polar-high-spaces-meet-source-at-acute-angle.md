---
rg: 2
id: atlas-six-row-polar-high-spaces-meet-source-at-acute-angle
kind: claim
title: Initial and final residual high spaces meet the Atlas source at an acute principal angle
refuted_by: atlas-affine-acute-angle-forces-two-point-k-orbit
distinct_from:
  atlas-six-row-singular-counting-dominates-nontrivial-s3: that asks only a rank bound with an unspecified constant; this asks the concrete stronger geometric statement that the source has no vector orthogonal to all twelve moving initial/final high spaces and would give constant two.
  atlas-pointwise-column-coercivity-misses-moving-injection: that rules out deriving transversality from tracially functorial unthresholded column positivity; this imposes transversality only after taking the finite-coordinate spectral projections.
---

**REFUTED.**  The proposed statement was the following.  For each of the six
residuals write its polar decomposition as

```text
R_r=V_r |R_r|,
Q_(r,t)=1_[kappa t,infinity)(|R_r|),
Q'_(r,t)=V_r Q_(r,t) V_r^*.                          (PAI1)
```

Thus `Q_(r,t)` and `Q'_(r,t)` are respectively the initial and final
high-singular spaces and have the same rank.  Put

```text
P_t=1_[t,infinity)(|U-E_K(U)|),
Z_t=join_r (Q_(r,t) join Q'_(r,t)).                  (PAI2)
```

Prove a constant `kappa in (0,1]`, independent of external regular
multiplicity, such that every finite regular frame and every `0<t<=2`
satisfy

```text
||(1-Z_t)P_t||_op < 1.                               (PAI3)
```

Equivalently, the largest principal angle from `Ran(P_t)` to `Ran(Z_t)` is
strictly less than `pi/2`, or

```text
Ran(P_t) intersect Ker(Z_t)={0}.                     (PAI4)
```

No uniform margin below one is required: finite-dimensional injectivity is
enough.  The incidence in `(PAI1)--(PAI2)` depends on the complete matrix
coordinate `U` and on `t`; it is not a fixed packet graph.

The characteristic-two affine enemy refutes it.  There only the collision
residual survives and is self-adjoint, so `Z_t` has normalized rank `1/2`.
The exact orbit-rank calculation in
`atlas-affine-acute-angle-forces-two-point-k-orbit` gives normalized source
rank at least `2/3` for every sufficiently small threshold.  Hence
`Z_t:Ran(P_t)->Ran(Z_t)` cannot be injective and `(PAI3)` fails for every
choice of `kappa`.

The Leavitt factor violates the tracial analogue because every `Q_r,Q'_r`
is zero while `P_t` is nonzero for a positive-measure set of thresholds.
Thus any proof of `(PAI3)` must use finite-coordinate integrality after the
spectral selection, exactly as required by the parent singular-counting gate.

## Attempts

- **Affine falsification is complete.**
  `atlas-affine-acute-angle-forces-two-point-k-orbit` first reduces the source
  rank to the raw-`S3` orbit size.  The archived dual functionals then prove
  that the raw three-cycle does not fix the quotient vector.  Thus the orbit
  has size `3` or `6`, the source rank is at least `2/3`, and the half-rank
  collision target cannot receive an injection.
- **Unthresholded column coercivity is fenced.**  The route
  `atlas-moving-singular-injection-via-residual-column-coercivity` is
  invalidated in its fixed-tracial form.  A successful proof must use the
  post-threshold initial/final ranges themselves, not obtain their
  transversality from a Gram inequality valid in arbitrary finite factors.
- **Adding an angle margin cannot help.**  The counterexample already has a
  nonzero kernel for the proposed projection, not merely angles converging to
  `pi/2` under amplification.
