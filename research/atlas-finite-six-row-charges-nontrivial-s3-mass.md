---
rg: 2
id: atlas-finite-six-row-charges-nontrivial-s3-mass
kind: claim
title: The joint six-row defect charges all nontrivial collision-channel mass in finite regular frames
distinct_from:
  atlas-finite-nontrivial-s3-shell-pays-boundary: that false target discarded collision after using it to enter a positive-mass shell; this keeps the collision defect on the charging side and is not refuted by the finite affine boundary model.
  atlas-six-relator-factor-retains-half-nontrivial-s3-mass: that refutes the same inequality in the exact Leavitt factor; this asks for it only in finite regular matrix coordinates and therefore isolates the CE category boundary exactly.
  atlas-19243-forces-sign-or-standard-channel-mass: that lower-bounds one nontrivial channel from small collision defect; this asks the full joint six-row defect to upper-bound their aggregate mass.
  atlas-typed-hard-interior-comb-row-census: that selects one extension-labelled incidence carrying five operator paths; this asks only for aggregate diagonal-S3 channel mass and has no S4 label or nuisance minor.
  atlas-six-relator-relative-h-bridge-gap: that controls four bridge words generating the full H=GL3(2); this controls only the two nontrivial central isotypes for the collision K=S3 and uses the collision wall to recover a scalar contradiction.
  atlas-two-s3-covariance-collapse: that uses the full canonical Atlas packet in an asymptotic implication; this uses only the five selected boundary words and c_19243 in one quantitative finite-matrix inequality.
---

**OPEN.**  Let `K=<h_a,h_b>~=S3` be the collision subgroup.  Decompose a
regular common-frame unitary under diagonal `K` conjugation as

```text
U=U_1+U_epsilon+U_sigma,
m_nt(U)=||U_epsilon||_2^2+||U_sigma||_2^2,             (JSC1)
```

and put

```text
D_6(U)=sum_(j in {0,11,30,44,55})||pi_U(s_j)-1||_2^2
                         +||pi_U(c_19243)-1||_2^2.    (JSC2)
```

Prove one constant `C_S3<infinity`, independent of the external regular
multiplicity, such that every finite regular common frame satisfies

```text
m_nt(U)<=C_S3 D_6(U).                                 (JSC3)
```

If `e_K(U)` is the two-generator collision covariance energy, the sign
channel has Laplacian eigenvalue `8` and the standard channel has eigenvalues
`2,6`.  Hence

```text
2m_nt(U)<=e_K(U)<=8m_nt(U).                            (JSC3a)
```

Thus `(JSC3)` is equivalently a two-fixed-bridge charge up to constants, but
it is strictly smaller than controlling all four standard `H` bridges.

This is a genuinely joint boundary--collision statistic.  The finite
characteristic-two affine frame does not refute it: that model has boundary
defect zero and `m_nt>=1/2`, but its collision-centrality defect squared is
exactly `2`.  It only imposes the calibration `C_S3>=1/4`.

The exact Leavitt factor does refute the universal tracial analogue.  There
all six defects vanish while
`atlas-six-relator-factor-retains-half-nontrivial-s3-mass` gives
`m_nt>=1/2`.  Thus `(JSC3)` cannot be a star-polynomial identity, a tracial
sum of squares, or a finite-von-Neumann dimension inequality.  It must use a
specifically matricial operation which fails on that non-CE candidate face.

## Exact relation to the scalar floor

`atlas-joint-s3-charge-gives-six-relator-floor` proves that `(JSC3)` implies
the explicit scalar bound

```text
D_6(U)>=2/(1+16 sqrt(2C_S3))^2.                       (JSC4)
```

Conversely, if `D_6(U)>=eta_6>0`, then orthogonality of the three `S3`
channels and `||U||_2=1` give `m_nt(U)<=1<=D_6(U)/eta_6`.  Hence the scalar
floor implies `(JSC3)` with `C_S3=1/eta_6`.  The two claims are therefore
quantitatively equivalent, but `(JSC3)` exposes a smaller representation-
theoretic payload: charge one fixed positive Fourier component rather than
exclude the entire unitary locus without a witness.

## Attempts and admissible proof shape

- Boundary-only charging is refuted in finite matrices by the affine model;
  `c_19243` must remain on the right of `(JSC3)`.
- Universal six-row charging is refuted by the exact Leavitt factor; the
  needed estimate must distinguish finite matrices from that factor.
- Fixed congruence, determinant, parity, and bounded rank corrections vanish
  under external amplification and cannot supply `C_S3`.
- **Fixed Reynolds--Gram charging is refuted.**  The route
  `atlas-joint-s3-charge-from-fixed-reynolds-gram` allows the exact diagonal
  `S3` expectation, separate sign/standard blocks, fixed operator-valued
  Gram matrices, Schur complements, and sums of squares.  All those
  operations extend to finite tracial factors, where the exact Leavitt model
  has `D_6=0` and `m_nt>=1/2`.  Therefore channel splitting is useful only
  upstream of a dimension-dependent finite-coordinate selection; fixed
  blockwise positivity cannot close `(JSC3)`.
- **First dimension-dependent gate.**
  `atlas-six-row-singular-counting-dominates-nontrivial-s3` asks whether, at
  every threshold, the moving high-singular-value projection of
  `U-E_K(U)` is covered in normalized rank by the six residual high-spectrum
  projections at a proportional threshold.  The exact layer-cake route
  `atlas-singular-counting-layer-cake-proves-joint-s3-charge` turns constants
  `(C_rank,kappa)` into `C_S3=C_rank kappa^(-2)`.  Unlike naive HS-to-rank
  decoding, this claim scales the residual threshold with the source
  threshold and does not attempt a multiplicative clipping.
- A valid proof may work separately on the sign and standard central
  idempotents, but both estimates must retain the collision residual or a
  mixed boundary--collision coefficient.  Merely proving positive channel
  mass from collision and then applying a boundary-only estimate repeats the
  refuted shell route.
