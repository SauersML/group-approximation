---
rg: 2
id: fano-cap-sequential-products-form-an-algebraic-naimark-carrier
kind: claim
title: Fano-cap sequential products form one noncentral algebraic Naimark carrier
distinct_from:
  fano-maximal-cap-overlap-has-positive-sequential-mass: that records a scalar trace identity and extracts one nonzero profile; this keeps every profile and upgrades the cover identity to a rectangular algebraic isometry.
  tracial-cap-menus-are-central-core-partitions: that classifies exact tracial branch decompositions; the carrier here is deliberately nonreducing and its profile diagonals compress to POVM effects rather than branch projections.
---

**ESTABLISHED, BUT NOT AN AFFINE-BRANCH SELECTOR.**  Let `A` be a unital
star algebra and, for `1<=c<=m`, let

```text
E_(c,lambda)=E_(c,lambda)^*=E_(c,lambda)^2,
sum_(lambda in Lambda) E_(c,lambda)=r 1.               (FNC1)
```

No commutation is assumed between different values of `c`.  For a profile
`boldlambda=(lambda_1,...,lambda_m)`, put

```text
K_boldlambda=r^(-m/2)
 E_(m,lambda_m)...E_(1,lambda_1).                      (FNC2)
```

When `r` is a square in the coefficient field, these are algebraic
coefficients.  They satisfy the exact column identity

```text
sum_boldlambda K_boldlambda^* K_boldlambda=1.          (FNC3)
```

Thus the column `V=(K_boldlambda)_boldlambda` is a rectangular algebraic
isometry and

```text
Q=VV^* in M_(|Lambda|^m)(A)                            (FNC4)
```

is a nonzero algebraic projection.  The map

```text
rho:A -> Q M_(|Lambda|^m)(A) Q,
rho(a)=VaV^*                                             (FNC5)
```

is a unital star homomorphism with corner unit `Q`.  Moreover the column is
an exact right-residual tight frame:

```text
sum_boldlambda ||K_boldlambda R||_2^2=||R||_2^2         (FNC6)
```

in every tracial representation of `A`.

For the seven maximal Fano-cap projections, `|Lambda|=7` and `r=4`, so the
normalizing coefficient in `(FNC2)` is the rational scalar `2^(-m)`.  This
gives an exact algebraic upgrade of
`fano-maximal-cap-overlap-has-positive-sequential-mass`: it packages all
`7^m` sequential profiles into one common noncentral carrier instead of
choosing a largest scalar overlap.

## Normalized corner trace and a finite-group host

Suppose `A=q C[Gamma] q`, with `q!=0`, and normalize its canonical corner
trace by

```text
tau_A(a)=tau_Gamma(a)/tau_Gamma(q).                     (FNC7)
```

With `N=|Lambda|^m`, use the unnormalized matrix trace `Tr_N` on
`M_N(A)`.  Then

```text
(Tr_N tensor tau_A)(Q)=tau_A(V^*V)=1.                  (FNC8)
```

Consequently `Q` has trace `1/N` for the normalized ambient trace
`tr_N tensor tau_A`, and the normalized trace on the corner `Q M_N(A) Q`
pulls back under `(FNC5)` exactly to `tau_A`.

This matrix amplification has a finite-group-algebra realization.  Choose a
finite group `F` with an irreducible complex representation `sigma` of
dimension `N`; for example, for `N>=2` take the standard representation of
`S_(N+1)`.  If `p_sigma` is the corresponding primitive central projection,
then

```text
(p_sigma tensor q) C[F times Gamma] (p_sigma tensor q)
  isomorphic to M_N(q C[Gamma] q).                     (FNC9)
```

Under this isomorphism `Q` is a finite-support group-algebra projection.  Its
canonical trace is positive, and its normalized trace inside the host
corner is exactly `1/N`.  Thus `(FNC4)` is an authenticated Hecke carrier;
no polar decomposition or representation-dependent support projection is
used.

## The sharp profile-diagonal boundary

Let `L_lambda` be the external diagonal projection onto label `lambda` in
the one-context construction.  Then

```text
V^* L_lambda V=E_lambda/r.                             (FNC10)
```

For the Fano cover this is `E_lambda/4`, which is not a projection whenever
`E_lambda!=0`.  Equivalently, `L_lambda` does not commute with `Q`.  The
external sharp label PVM therefore restricts to a POVM on the represented
copy `(FNC5)`, not to a cap-branch PVM.

This failure is quantitative.  With the unnormalized matrix trace from
`(FNC8)`,

```text
||[Q,L_lambda]||_2^2
 =2 tau_A(E_lambda)(1/r-1/r^2),                        (FNC11)

sum_lambda ||[Q,L_lambda]||_2^2=2(1-1/r).             (FNC12)
```

For the Fano cover the total mixing energy is `3/2`.  It is therefore not a
small defect that could be discarded while retaining exact completeness.

This is load-bearing.  If a profile diagonal were made into a genuine exact
branch for `(FNC5)`, its compression would have to be multiplicative.  The
equality case of the two Schwarz identities then forces that diagonal to
reduce `rho(A)`.  Its restricted trace is consequently a central-type
decomposition of the represented model, returning exactly to the firewall
in `tracial-cap-menus-are-central-core-partitions`.  In particular the
carrier `(FNC4)` cannot be inserted into the finite affine-branch OR as if it
selected one Fano cap.

The surviving use is narrower and genuinely noncentral: `(FNC6)` may pack
profile-indexed **right residual energies** into one authenticated Hecke
carrier.  Any coefficient-link application must exploit that interference
identity directly.  Requiring sharp persistent cap records would turn the
construction back into a reducing selector (and, for several sharp source
PVMs, into a joint-measurability/commutation demand).
