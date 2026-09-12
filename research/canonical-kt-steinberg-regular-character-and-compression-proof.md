---
rg: 2
id: canonical-kt-steinberg-regular-character-and-compression-proof
kind: route
title: Build the KT regular Steinberg tower and compute its deleted-line commutants
target: kt-steinberg-deleted-line-embeddings-have-scalar-commutants
requires:
  - el-r-polynomial-robust-spectral-gap
  - strict-compressor-mixed-return-collapses-shared-pauli-sign
  - kt-deleted-line-instability-cannot-carry-majorana-wall
---

# The canonical congruence sector contains strict instability but no commutant leak

All matrix `2`-norms below are normalized.  The symbol `||.||_F` denotes
the unnormalized Frobenius norm.

## 1. A full-actor Steinberg representation

Fix `r>=3` and put

```text
R_+ = F_2[x_1,x_2,x_3],
R   = F_2[x_1^(+-1),x_2^(+-1),x_3^(+-1)],
Gamma = EL_r(R_+),
G = EL_r(R) semidirect SL_3(Z).
```

For an odd prime `m`, set

```text
V_m = (Z/mZ)^3,
A_m = F_2[V_m],
E_m = EL_r(A_m),
Q_m = E_m semidirect SL_3(Z/mZ).                         (1)
```

Reduction of Laurent exponents modulo `m` and reduction of the actor modulo
`m` give a homomorphism `q_m:G->Q_m`.

The algebra `A_m` is commutative semisimple because `m` is odd.  Over the
algebraic closure its characters are indexed by `V_m`, and Frobenius acts
as

```text
v |-> 2v.                                                (2)
```

Let `Omega_m` be the set of Frobenius orbits.  If `O in Omega_m` has size
`f_O`, then

```text
A_m = product_(O in Omega_m) F_(2^f_O),
E_m = product_(O in Omega_m) SL_r(F_(2^f_O)).            (3)
```

For each `O` let `Delta_O` be the spherical building of
`SL_r(F_(2^f_O))` and let

```text
St_O = reduced H_(r-2)(Delta_O;C)                        (4)
```

be its Steinberg module.  Define `Delta_m` to be the simplicial join of all
the `Delta_O`.  The group `E_m` acts factorwise.  The actor
`SL_3(Z/mZ)` acts on `A_m`, permutes its primitive field factors, and
induces semilinear building isomorphisms.  It therefore acts simplicially
on `Delta_m`.  Consequently top reduced homology gives an actual complex
representation

```text
alpha_m^0 : Q_m -> U(H_m),
H_m = tensor_(O in Omega_m) St_O,                        (5)
```

up to the harmless orientation sign from permuting join factors.  This
construction is why there is no projective-extension obstruction.  Compose
with `q_m` and write the result as `alpha_m`.

The Steinberg degree formula gives, for
`N=r(r-1)/2`,

```text
dim St_O = 2^(N f_O),
D_m := dim H_m
     = product_O 2^(N f_O)
     = 2^(N m^3).                                        (6)
```

The restriction of (5) to `E_m` is the external tensor product of
irreducible representations of the direct factors in (3), hence is
irreducible.

The ring map `R_+->A_m` is onto: in `A_m` one has
`x_i^(-1)=x_i^(m-1)`.  Thus `Gamma` maps onto `E_m`.  If
`Lambda=t Gamma t^(-1)` for a compressor `t in G`, then

```text
q_m(Lambda)
 = q_m(t) E_m q_m(t)^(-1)
 = E_m,                                                  (7)
```

because `E_m` is normal in `Q_m`.  Therefore

```text
alpha_m|Gamma and alpha_m|Lambda are irreducible,
alpha_m(Gamma)=alpha_m(Lambda)=alpha_m(E_m).             (8)
```

In particular both exact coordinate commutants are scalar.

## 2. The normalized characters become regular

Choose any sequence of distinct odd primes tending to infinity and put

```text
f_m = ord_m(2).                                          (9)
```

Then `f_m->infinity`.  Indeed, primes with `ord_m(2)<=B` divide one of the
finitely many integers `2^j-1`, `1<=j<=B`.

We use the standard Steinberg character estimate

```text
|chi_St(h)| / chi_St(1) <= |K|^(-1)                     (10)
```

for every noncentral `h in SL_r(K)`.  For completeness, the Steinberg
character vanishes off the semisimple set.  At a semisimple element it is,
up to sign, the characteristic-prime part of the centralizer order.  A
noncentral semisimple element of `SL_r(K)` has a proper root centralizer, so
that prime part is at most `|K|^(N-1)`, while the Steinberg degree is
`|K|^N`.  This proves (10).  This is the usual Steinberg character formula;
only the coarse one-power saving is used here.

Take a fixed nonidentity `g=(e,A) in G`.

### 2a. A nontrivial actor moves a growing field factor

Suppose first that `A!=I`.  The actor action on the character group `V_m`
commutes with the scalar Frobenius action (2).  If `A` fixed every
Frobenius orbit, then for every nonzero `v in V_m` there would be an integer
`k(v)` such that

```text
A v = 2^k(v) v.                                          (11)
```

Thus every vector would be an eigenvector.  Applying this to two independent
vectors and their sum shows that `A` is scalar modulo `m`.

A fixed integral matrix `A in SL_3(Z)` can be scalar modulo infinitely many
growing primes only if all its off-diagonal entries vanish and its diagonal
entries agree over `Z`.  Its determinant then forces `A=I`.  Hence, for all
large `m`, a nonidentity `A` moves some nonzero orbit `O`.  Every nonzero
orbit has size `f_m`, because `m` is prime.

On a cycle of length `ell>=2` of equal-dimensional tensor factors, a
weighted cyclic permutation has trace equal, up to sign, to the trace of
the product of the `ell` transition maps.  If the factor dimension is
`a`, its normalized trace has absolute value at most

```text
a / a^ell <= 1/a.                                       (12)
```

The elementary component `e` merely changes the unitary transition maps.
For the moved factor, `a=2^(N f_m)`.  Therefore

```text
|tr_(D_m)(alpha_m(e,A))| <= 2^(-N f_m) -> 0.            (13)
```

### 2b. A nontrivial elementary matrix is noncentral on a growing factor

Now suppose `A=I` and `e!=I`.  The matrix `e` is not a scalar Laurent
matrix.  Indeed, a scalar element of `SL_r(R)` has the form `lambda I` with
`lambda` a Laurent monomial and `lambda^r=1`; the Laurent exponent group is
torsion free and `F_2^*=1`, so `lambda=1`.  Choose a nonzero Laurent
polynomial `p` which is either an off-diagonal entry of `e` or a difference
of two diagonal entries.

For all sufficiently large odd primes `m`, the polynomial `p` does not
vanish at every nontrivial `m`-torsion point of the three-dimensional torus.
Here is a direct finite Fourier proof.  Shift the finite exponent support of
`p` into a fixed box.  For `m` larger than that box, reduction modulo
`x_i^m-1` creates no collisions.  If the resulting function on the
`m`-torsion characters vanished away from the identity, Fourier inversion
over `F_2[V_m]` would make its coefficient vector either zero or a nonzero
constant on all `m^3` group elements.  The first option contradicts
`p!=0` and the second contradicts the fixed finite support of `p`.

Thus there is a nonzero `v in V_m` at which the evaluated matrix is
noncentral.  Its Frobenius orbit has size `f_m`, so the corresponding field
factor is `F_(2^f_m)`.  Formula (10), followed by factorization of the
external tensor character, gives

```text
|tr_(D_m)(alpha_m(e,I))| <= 2^(-f_m) -> 0.              (14)
```

Equations (13)--(14) prove

```text
tr_(D_m)(alpha_m(g)) -> 0 for every g!=1.               (15)
```

Thus the congruence tower has the regular character of the full actor, not
merely of `Gamma`.

## 3. Delete one line

Choose any rank-`d_m=D_m-1` projection `P_m` and identify

```text
H_m = P_m H_m direct_sum C.
```

For `g in G`, write `U=alpha_m(g)` and let `B=P_m U P_m` on `P_m H_m`.
Since

```text
I-B^*B = P_m U^*(1-P_m)U P_m                            (16)
```

has rank at most one, all but at most one singular value of `B` equal one.
Choose a unitary polar completion `rho_m(g)` of `B`.  The singular-value
calculation gives

```text
||rho_m(g)-B||_F^2
 <= Tr(I-B^*B) <= 1.                                    (17)
```

The two off-diagonal blocks of `U` each have Frobenius norm at most one, and
the missing scalar block differs from `1` by at most two.  Hence

```text
||alpha_m(g)-(rho_m(g) direct_sum 1)||_F^2 <= 7.         (18)
```

We may therefore use the universal constant `C_0=3`.

Put `W_m(g)=rho_m(g) direct_sum 1`.  Exact multiplication of `alpha_m` and
(18) imply, for fixed `g,h`,

```text
||W_m(g)W_m(h)-W_m(gh)||_(2,D_m)
 <= 3 C_0 / sqrt(D_m).                                  (19)
```

The difference in (19) is zero on the last scalar block.  Rescaling to
dimension `d_m` proves that `rho_m` is pointwise asymptotically
multiplicative.  Choose `rho_m(1)=I`.  Thus

```text
rho(g)=[rho_m(g)]
```

is a homomorphism into the tracial matrix ultraproduct.

Moreover,

```text
|tr_(d_m)(rho_m(g))-tr_(D_m)(alpha_m(g))|
 <= C_0/sqrt(D_m)+2/D_m.                                (20)
```

Together with (15), this says that `rho` has the regular character.  It is
injective and extends to a trace-preserving embedding of `L(G)` into the
matrix ultraproduct.

## 4. Strict same-dimensional lifting is impossible

Let `S` be a finite Kazhdan set for `Gamma` and let `kappa>0` have the
convention

```text
max_(s in S)||pi(s)xi-xi|| >= kappa dist(xi,H^Gamma).    (21)
```

Let `J_m:P_m H_m->H_m` be the inclusion.  Equation (18) implies

```text
max_(s in S)
 ||alpha_m(s)J_m-J_m rho_m(s)||_(F) <= C_0.             (22)
```

Take any genuine representation `beta_m:Gamma->U(d_m)`.  On
`Hom(P_m H_m,H_m)` consider the exact unitary representation

```text
T |-> alpha_m(s) T beta_m(s)^*.                          (23)
```

Its invariant subspace is `Hom_Gamma(beta_m,alpha_m)`.  It is zero:
a nonzero intertwiner would have nonzero invariant image, hence would
surject onto the irreducible `D_m`-dimensional representation
`alpha_m|Gamma` from a `d_m`-dimensional space.

The inclusion `J_m` has normalized Hom Hilbert--Schmidt norm one.  Applying
(21) to (23), and then (22), yields

```text
max_(s in S)||rho_m(s)-beta_m(s)||_(2,d_m)
 >= kappa-C_0/sqrt(d_m).                                 (24)
```

This proves the strict nonliftability bound.  Replacing `S` by
`t S t^(-1)` gives the identical statement for `Lambda`.

On the other hand, (18) says uniformly on every finite subset of `G` that
one-dimensional padding recovers the exact congruence representation.
Strict instability and flexible congruence therefore coexist.

## 5. The inexact commutants are scalar

The crucial point is that the same Kazhdan gap used in (24) also eliminates
every approximate multiplicity operator.

Let `x_m in M_(d_m)` be contractions and put

```text
Y_m=J_m x_m J_m^* in M_(D_m).                            (25)
```

For `s in S`, two uses of (22) give

```text
||alpha_m(s)Y_m alpha_m(s)^*-Y_m||_(2,D_m)
 <= sqrt(d_m/D_m)
       ||rho_m(s)x_m rho_m(s)^*-x_m||_(2,d_m)
    + 2 C_0/sqrt(D_m).                                  (26)
```

Apply the Kazhdan distance-to-invariants inequality to the exact conjugation
representation `Ad alpha_m|Gamma`.  Its invariant space is

```text
alpha_m(Gamma)' = C I_(D_m)                              (27)
```

by (8).  If

```text
delta_m=max_(s in S)||[x_m,rho_m(s)]||_(2,d_m),
```

then (26)--(27), followed by restriction back to `P_m H_m`, give the explicit
low-band estimate

```text
dist_(2,d_m)(x_m,C I_(d_m))
 <= delta_m/kappa + 2 C_0/(kappa sqrt(d_m)).             (28)
```

Consequently, if `x=[x_m]` commutes with `rho(Gamma)` in the ultraproduct,
then `x` is scalar.  The same proof for the conjugate Kazhdan set and the
second irreducibility statement in (8) gives

```text
rho(Gamma)'=C=rho(Lambda)'.                              (29)
```

This is an inexact-coordinate instance of the Alekseev--Thom coordinate
commutant conclusion: take the coordinate algebras to be
`C I_(d_m)`.  Scalars are automatically coherent under conjugation by every
actor matrix.

Estimate (28) also gives the named mixed-return modulus directly.  For every
fixed `u in G`,

```text
||rho_m(u)x_m rho_m(u)^*-x_m||_(2,d_m)
 <= 2 delta_m/kappa + 4 C_0/(kappa sqrt(d_m)).           (30)
```

Thus every low-energy `Gamma`-central contraction is fixed by the mixed
return from `strict-compressor-mixed-return-collapses-shared-pauli-sign`.
In the language of that node, the low-band operator-norm leakage is zero on
this tower.

## 6. Exact scope

This construction proves three facts simultaneously.

1. Regular character does not force literal same-dimensional coordinate
   exactness, even for the canonical KT congruence sector.
2. Negligible-rank failure of exactness is removed by the flexible padding in
   Open Problem 6.2.
3. Irreducibility plus property `(T)` makes that failure invisible to the
   relative commutant; both compressor copies have scalar commutant.

Therefore a genuine countermodel to KT commutant normalization cannot be a
single regular irreducible with a small deleted boundary.  It must retain a
positive-density multiplicity algebra through every `o(d)` correction.  No
such KT source-specific model is constructed here, and no universal
classification of trace-faithful embeddings is claimed.  The global route
remains open.

## Source pins

- Kun--Thom, arXiv:2608.06222: the binary Laurent elementary actor,
  congruence quotients, strict compressors, and universal-sofic
  centralizer normalization.
- Alekseev--Thom, arXiv:2608.05362, Open Problem 6.2: coordinate
  commutants for Kazhdan hyperlinear representations.
- Solomon--Tits and the standard building model of the Steinberg
  representation: (4)--(6).
- The standard Steinberg character formula
  `St(h)=0` off semisimple elements and
  `|St(h)|=|C(h)|_2` on semisimple elements, up to sign: estimate (10).

No stability theorem is used to construct `rho_m`; all correction and
commutant estimates are the displayed rank-one calculation plus the Kazhdan
gap.
