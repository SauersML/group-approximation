---
rg: 2
id: kt-steinberg-deleted-line-embeddings-have-scalar-commutants
kind: claim
title: Canonical KT Steinberg deleted-line embeddings are strictly unstable but have scalar relative commutants
artifacts:
  - research/canonical-kt-steinberg-regular-character-and-compression-proof.md
distinct_from:
  ccr-for-coordinate-collapsing-models: that treats ultraproducts of genuine coordinate representations; this constructs an everywhere-inexact trace-faithful embedding, proves strict same-dimension nonliftability, and still computes both compressed-copy commutants.
  at-op62-holds-for-representation-lifts: that assumes the lifts are representations; these lifts are not representations in any coordinate and remain a uniform distance from every same-dimensional representation of Gamma.
  kt-deleted-line-instability-cannot-carry-majorana-wall: that rules out a Pauli wall for a generic deleted-line family once a suitable genuine actor family is supplied; this constructs an explicit regular-character congruence family for the full KT actor and identifies its relative commutants.
  congruence-twist-survives-flexible-moving-padding: that builds a padding-stable obstruction to monomialization for SL3(Z); the present obstruction is repaired by exactly one line and concerns representation lifting and matrix commutants, not monomial carriers.
  strict-compressor-mixed-return-collapses-shared-pauli-sign: that proves the exact-actor mixed-return estimate; this proves its ultraproduct conclusion for a concrete inexact regular-character sector.
---

**ESTABLISHED SPECIAL THEOREM; THE UNIVERSAL KUN--THOM / ALEKSEEV--THOM
QUESTION REMAINS OPEN.**

Pin the binary Kun--Thom actor

```text
R_+   = F_2[x_1,x_2,x_3],
R     = F_2[x_1^(+-1),x_2^(+-1),x_3^(+-1)],
Gamma = EL_r(R_+),                         r >= 3,
G     = EL_r(R) semidirect SL_3(Z),
Lambda = t Gamma t^(-1) < Gamma
```

for any strict positive compressor `t`.  There is an explicit sequence of
genuine congruence representations

```text
alpha_m : G -> U(D_m)
```

indexed by growing odd primes `m`, with all of the following properties.

1. The normalized characters of `alpha_m` converge pointwise to the regular
   character of `G`.
2. Both restrictions `alpha_m|Gamma` and `alpha_m|Lambda` are irreducible.
   In fact their images are the same finite elementary group.
3. If

   ```text
   A_m = F_2[(Z/mZ)^3],
   N = r(r-1)/2,
   ```

   then one may take

   ```text
   D_m = 2^(N m^3).
   ```

The construction is canonical: decompose the semisimple ring `A_m` into
finite-field factors indexed by Frobenius orbits, take the external tensor
product of the Steinberg modules of all factors, and use top homology of the
join of their spherical buildings.  Functoriality of the building gives an
actual, not merely projective, action of `SL_3(Z/mZ)`.

Now delete an arbitrary one-dimensional subspace.  If `P_m` has rank
`d_m=D_m-1`, let `rho_m(g)` be a unitary polar completion of

```text
P_m alpha_m(g) P_m
```

on `P_m C^(D_m)`.  These maps define a trace-faithful homomorphism

```text
rho : G -> U( product_U M_(d_m) ).
```

They give an explicit regular-character obstruction to **literal**
same-dimensional profinite exactification.  For a fixed Kazhdan set `S` of
`Gamma` and Kazhdan constant `kappa>0`,

```text
liminf_m inf_(beta_m:Gamma->U(d_m) exact)
  max_(s in S) ||rho_m(s)-beta_m(s)||_(2,d_m) >= kappa.       (KSD1)
```

The same statement holds for `Lambda` with the conjugate Kazhdan set.

Nevertheless the obstruction is exactly one-dimensional.  Under the
decomposition `C^(D_m)=P_m C^(D_m) direct_sum C`, there is a universal
constant `C_0` such that, for every `g in G`,

```text
|| (rho_m(g) direct_sum 1) - alpha_m(g) ||_(2,D_m)
   <= C_0 / sqrt(D_m).                                      (KSD2)
```

Thus the family is flexibly congruence after `o(d_m)` padding.  It does not
refute the padding allowed in Alekseev--Thom Open Problem 6.2.

More importantly, property `(T)` sees through the deleted line at the
commutant level:

```text
rho(Gamma)'  intersect product_U M_(d_m) = C,
rho(Lambda)' intersect product_U M_(d_m) = C.              (KSD3)
```

The conclusion is quantitative.  For contractions `X_m` and the same
Kazhdan data,

```text
dist_(2,d_m)(X_m,C)
 <= kappa^(-1) max_(s in S)||[X_m,rho_m(s)]||_(2,d_m)
    + 6/(kappa sqrt(d_m)).                                (KSD4)
```

Hence the coordinate algebras `C I_(d_m)` witness the coordinate-commutant
conclusion of Open Problem 6.2 for this everywhere-inexact embedding; every
requested conjugation coherence is automatic.  Formula (KSD4) makes every
fixed mixed-return leakage tend to zero, so the condition of
`strict-compressor-mixed-return-collapses-shared-pauli-sign` holds here and
the compressor commutant inclusion is equality.

**Boundary exposed.**  The assertion that every trace-faithful KT embedding
is literally a same-dimensional congruence tower is false already in this
canonical regular-character sector.  But the obstruction disappears after
one line and creates no excess commutant.  Therefore a counterexample to the
padded Alekseev--Thom statement or to Kun--Thom commutant normalization must
have both:

- padding-stable, positive-density nonliftability; and
- macroscopic multiplicity producing a non-scalar low-energy commutant.

An irreducible regular-character block with a negligible boundary has
neither feature.  The global nonhyperlinear-group route remains **OPEN**.

DERIVATION
canonical-kt-steinberg-regular-character-and-compression-proof
