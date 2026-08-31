---
rg: 2
id: two-raw-roots-have-a-uniform-full-carrier-gap
kind: claim
title: Two raw roots eliminate every constant-core false intertwiner
distinct_from:
  constant-core-gap-stops-at-k-intertwiners: that constructs an exact K-intertwiner outside the full-carrier intertwiner space; this proves the raw-root covariance packet detects it uniformly
  first-uncancelled-g2-mixed-carrier-has-no-hall-deficit: that computes polar support of one concrete two-letter qutrit carrier; this computes the full finite-section Hecke displacement
  elementary-group-property-t-over-free-algebras: that proves property T abstractly; this identifies its exact quotient action on the two-orientation Toeplitz carrier
---

Put `m=28`,

```text
F_N=GL_(mN)(F_2),
K=GL_m(F_2) tensor I_N,
a_L=I+E_ij tensor L,
```

where `L` is either truncated shift `S_N` or `T_N` and `N>=2`. Then

```text
K intersect a_L K a_L^(-1)=C_K(I+E_ij),                (TRG1)

|K a_L K/K|=(2^m-1)(2^(m-1)-1).                        (TRG2)
```

Let `d=[F_N:K]` and let `v` be the unit K-fixed, F-orthogonal base-coset
vector from `quasiregular-fixed-coset-produces-a-false-intertwiner-proof`.
For either raw root,

```text
||lambda_(F_N/K)(a_L)v-v||^2=2d/(d-1)>2.               (TRG3)
```

Thus the explicit false intertwiner has a dimension-independent covariance
floor greater than `sqrt(2)` as soon as one nonconstant root is tested.

More generally, the constant roots together with `a_(S_N)` and
`a_(T_N)` generate `F_N`. There is a constant `kappa>0`, independent of
`N` and of the carrier representations, such that every off-diagonal
operator `T` satisfies

```text
dist_(HS)(T,Hom_(F_N))
 <= kappa^(-1) max_(q in Q_N)
       ||pi_0(q)T-Tpi_1(q)||_(HS),                      (TRG4)
```

where `Q_N` is the fixed constant-core plus two-raw-root control packet.

Consequently there is no surviving Hecke spectral mode once covariance
under both raw orientations is available. The exact remaining gate is a
presentation-to-covariance compiler: the nonlinear long-router relators
must be shown to bound the right side of `(TRG4)` for the off-diagonal
coefficient. Relator defect alone does not supply this by
`presentation-defect-does-not-control-off-commutant-mass`.

DERIVATION
double-coset-degree-and-free-ring-kazhdan-proof
