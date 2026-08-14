# Central-regular Iwahori mismatch is confined to a sparse spectral outlier

Date: 2026-08-14

## 1. Outcome

The only unresolved Dogon--Vigdorovich Iwahori sequence has central-regular
limiting character on

```text
Gamma=SL_2(Z[1/2]).                                   (ICO1)
```

On either fixed central sector, form the exact mixed edge representation on
normalized Hilbert--Schmidt space

```text
Lambda_n(b)(T)=rho_n(b) T sigma_n(b)*.               (ICO2)
```

Its normalized character converges to the regular character of the
center-quotiented Iwahori group

```text
Bbar=B/<z> ~= Z * C_2.                               (ICO3)
```

Since `Bbar` is nonamenable, its regular random-walk Laplacian has a positive
bottom.  Consequently, below every fixed threshold smaller than that bottom,
the spectral projection of the mixed finite-dimensional Laplacian has
dimension `o(d_n^2)`.

The identity matrix is nevertheless an almost invariant unit vector for
`Lambda_n`, so it lies asymptotically inside this sparse low-energy space.
Thus every unresolved Iwahori pair has the precise form

```text
regular spectral bulk
 + an o(d_n^2)-dimensional outlier containing a full-rank
   near-intertwiner.                                  (ICO4)
```

This rules out diffuse mixed-gap collapse.  It does not yet prove flexible
matching: an `o(d_n^2)` operator subspace may contain an invertible matrix
(the scalar line is the simplest example), so Hilbert--Schmidt spectral
sparsity does not imply `o(d_n)` physical kernel/cokernel rank.

## 2. Mixed-character calculation

Let `rho_n,sigma_n:B->U(d_n)` be the two exact edge restrictions after
matching the central sign.  Their mixed action `(ICO2)` is an exact unitary
representation on the `d_n^2`-dimensional Hilbert space `M_(d_n)(C)`.

For left-right multiplication, the ordinary trace factorizes.  Hence the
normalized character is

```text
tr_(d_n^2)(Lambda_n(b))
 =tr_(d_n)(rho_n(b)) conjugate(tr_(d_n)(sigma_n(b))). (ICO5)
```

In the central-regular endpoint, both vertex traces converge to the same
central character:

```text
tr_(d_n)(rho_n(b)), tr_(d_n)(sigma_n(b)) -> 0
                                      if b notin <z>,
rho_n(z)=sigma_n(z)=chi(z)1.                          (ICO6)
```

Therefore

```text
tr_(d_n^2)(Lambda_n(b)) ->
  1,                         b in <z>,
  0,                         b notin <z>.             (ICO7)
```

The right side is exactly the regular character of `Bbar`, pulled back to
`B`.  Thus the mixed representations converge in normalized character to
the regular representation of the nonamenable group `(ICO3)`.

## 3. Empirical spectral convergence

Choose a finite symmetric generating multiset `S` of `Bbar` and use the
positive random-walk Laplacian

```text
Delta=1-(1/|S|)sum_(s in S) s                        (ICO8)
```

after symmetrizing so the displayed operator is self-adjoint.  Write
`Delta_n=Lambda_n(Delta)` and let `mu_n` be its empirical eigenvalue measure,
normalized by `d_n^2`.

For every polynomial `p`, equations `(ICO5)--(ICO7)` give

```text
integral p dmu_n
 =tr_(d_n^2)(p(Delta_n))
 ->tau_reg(p(Delta)).                                (ICO9)
```

All spectra lie in one fixed compact interval, so polynomial moment
convergence implies weak convergence

```text
mu_n -> mu_reg.                                      (ICO10)
```

Kesten's criterion and nonamenability of `Z*C_2` give a number `kappa>0`
such that

```text
supp(mu_reg) subset [kappa,infinity).                (ICO11)
```

Fix `0<a<kappa`.  Portmanteau applied to the closed interval `[0,a]` yields

```text
rank(1_[0,a](Delta_n))/d_n^2
 =mu_n([0,a]) ->0.                                   (ICO12)
```

This conclusion uses only normalized-character convergence and the regular
spectral gap.  It is independent of irreducible dimensions and
multiplicities.

## 4. The identity vector occupies the outlier

Let `xi_n=1_(d_n)`, viewed in normalized Hilbert--Schmidt space, so
`||xi_n||_2=1`.  The edge matching defect `delta_n->0` gives

```text
<Delta_n xi_n,xi_n> <= delta_n^2                    (ICO13)
```

up to the harmless choice of averaged/summed normalization in `(ICO8)`.
If `P_n=1_[0,a](Delta_n)`, spectral calculus gives

```text
a ||(1-P_n)xi_n||_2^2
 <=<Delta_n xi_n,xi_n>
 <=delta_n^2.                                       (ICO14)
```

Therefore

```text
||P_n xi_n-xi_n||_2 <=delta_n/sqrt(a) ->0.           (ICO15)
```

Equations `(ICO12)` and `(ICO15)` prove `(ICO4)`: the low-energy space has
vanishing relative Hilbert-space dimension but contains a vector converging
to the full-rank identity matrix.

## 5. Why this is not sparse physical padding

The mixed space has dimension `d_n^2`, whereas flexible representation
padding is measured in the physical dimension `d_n`.  No implication of the
form

```text
dim(E_n)=o(d_n^2),   E_n contains T_n near 1
       => rank defect of T_n=o(d_n)                  (ICO16)
```

is valid.  The one-dimensional subspace `C 1_(d_n)` already has dimension
`o(d_n^2)` and contains an invertible matrix of full rank.

Nor is the low-energy spectral projection a `B`-subrepresentation in
general: the random-walk Laplacian need not be central.  One cannot classify
`P_n M_(d_n)` as a small exact edge representation and pad it away without
an additional invariant-subspace repair.

Thus the new reduction does not silently assume the kernel-opening theorem
left open in `TRUE_IWAHORI_MIXED_GAP_DICHOTOMY.md`.

## 6. Corrected next theorem

The mixed-gap dichotomy can now be sharpened.  In the central-regular
endpoint, every obstruction is an **outlier localization problem**, not a
bulk spectral problem:

> **Full-rank outlier repair.**  Let exact Iwahori mixed representations
> converge in character to the regular representation of `Z*C_2`, and let
> their low-energy `o(d_n^2)` subspaces contain matrices converging to the
> identity in normalized Hilbert--Schmidt norm.  Use the fact that these
> matrices arise from restrictions of two exact `SL_2(Z)` representations
> to perturb the vertex representations by `o(d_n)` dimensions until the
> low-energy vector becomes an exact invertible intertwiner.

The italicized extension origin is essential.  For arbitrary representations
of `Z*C_2`, near-trivial one-dimensional characters give exactly such
outliers and need not contain invariant vectors.

A proof of full-rank outlier repair answers the Dogon--Vigdorovich matching
question positively and yields their explicit nonhyperlinear central
extension.  The result above removes the regular bulk from that theorem and
leaves only a vanishing-density spectral spike with a prescribed full-rank
vector.

## Primary inputs

- Dogon--Vigdorovich, *Hyperlinearity, stability and asymptotic spectral gap
  of higher rank lattices*, [arXiv:2506.20843v2](https://arxiv.org/abs/2506.20843v2),
  for the central-regular reduction and the conditional nonhyperlinear
  candidate.
- Kesten's amenability criterion for the positive regular spectral bottom of
  a finitely generated nonamenable group.

No local computation or build was run for this note.
