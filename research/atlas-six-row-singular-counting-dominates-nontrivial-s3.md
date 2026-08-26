---
rg: 2
id: atlas-six-row-singular-counting-dominates-nontrivial-s3
kind: claim
title: Six residual singular-counting functions cover the nontrivial collision channel in finite coordinates
distinct_from:
  atlas-finite-six-row-charges-nontrivial-s3-mass: that asks only for one quadratic normalized-Hilbert--Schmidt inequality; this is a stronger pointwise incidence statement for the moving singular subspaces at every scale.
  hs-full-rank-scalar-defect-blocks-naive-rank-decoding: that refutes an unscaled conversion from small Hilbert--Schmidt defect to small algebraic rank and multiplicatively coherent clipping; this compares source and residual ranks at proportional spectral thresholds and performs no clipping or correction.
  atlas-spectral-shrunk-intertwiner-certificate: that asks one low-energy operator space to have a shrunk input subspace; this directly compares the singular counting function of the nontrivial collision component with the six residual counting functions.
---

**OPEN.**  Retain the notation of
`atlas-finite-six-row-charges-nontrivial-s3-mass`.  For a finite regular common
frame put

```text
A(U)=U-E_K(U)
R_j(U)=pi_U(s_j)-1,                  j in {0,11,30,44,55},
R_c(U)=pi_U(c_19243)-1.                              (SCI1)
```

For a finite matrix `T` and `t>0`, write

```text
N_T(t)=tr_d(1_[t,infinity)(|T|)),                    (SCI2)
```

the normalized number of singular values at least `t`.  Prove constants
`C_rank<infinity` and `kappa in (0,1]`, independent of the regular external
multiplicity, such that every such frame and every `0<t<=2` satisfy

```text
N_A(t)
 <= C_rank (sum_j N_(R_j)(kappa t)+N_(R_c)(kappa t)). (SCI3)
```

This is the first literal finite-coordinate rank-incidence version of the
six-row problem.  The selected projections in `(SCI2)` move with both the
matrix coordinate and the threshold.  No common residual kernel, fixed
Fourier block, or multiplicatively coherent spectral clipping is requested.
Consequently the full-rank scalar-defect example does not formally refute
`(SCI3)`: scaling a residual by `epsilon` also scales the threshold at which
its rank is read.

## Exact calibrations

- For an aligned frame, `A=0`, so `(SCI3)` is automatic.
- In the characteristic-two affine frame the five boundary residuals vanish,
  while `pi_U(c_19243)` is a nonidentity involution in a regular
  representation.  Hence `|R_c|` has singular value `2` on normalized rank
  `1/2` and singular value `0` on the complement.  Since `kappa t<=2` and
  `N_A(t)<=1`, that archived enemy satisfies `(SCI3)` for every threshold as
  soon as `C_rank>=2`.  Thus the finite affine obstruction to boundary-only
  charging does not refute this joint rank incidence.
- The exact Leavitt factor has all six residuals zero and nontrivial-channel
  mass at least `1/2`.  Therefore the Murray--von Neumann spectral-projection
  analogue of `(SCI3)` is false in finite tracial factors.  Any proof must use
  a genuinely finite-matrix incidence or integrality input; a dimension-free
  von Neumann rank argument would repeat the already-refuted universal route.

The constants are allowed to be coarse.  The point is that normalized rank is
unchanged by external amplification, while a threshold chosen as `kappa t`
still records the amplitude of a full-rank small residual.  This is exactly
the finite arithmetic information lost by fixed Reynolds--Gram positivity.

## Attempts

- Taking the common kernel or the unthresholded algebraic ranks of the six
  residuals dies on full-rank scalar perturbations: an arbitrarily small
  scalar residual has zero kernel and normalized rank one.  The proportional
  threshold in `(SCI3)` is the minimal repair that retains amplitude.
- A fixed operator inequality between `A^*A` and the six residual squares
  would extend to finite tracial factors and is refuted by the exact Leavitt
  model.  The remaining attack is therefore deferred to a moving
  finite-coordinate incidence: select the spectral range of `|A|` at `t` and
  inject or Hall-match it into the six spectral ranges at `kappa t`, using
  integer matrix dimensions before normalizing.

