# The amenable conjugacy orbit has no internal Bernoulli commutant wall

Date: 2026-08-12

## 1. Outcome

Let `Gamma<G`, `h in G`, and

```text
S=C_G(h)
```

be the fully framed pair constructed in
`FALSE_FULLY_FRAMED_AMENABLE_CONJUGACY_ORBIT.md`.  Thus `Gamma` is a
nonamenable property-`(T)` group, `S` is amenable, and the transitive action

```text
G curvearrowright G/S
```

has the root-dependent sofic Schreier charts supplied by the
amenable-stabilizer theorem.

The most direct way to turn those charts into the relative-commutant wall
from `FALSE_RELATIVE_BICOMMUTANT_ENDPOINT.md` is to put a Bernoulli or Pauli
fiber over every point of `G/S`.  This note proves that this cannot work,
even after taking the tracial ultrapower of the resulting crossed product.

More precisely, let `(A_0,tau_0)` be a nontrivial separable finite tracial
von Neumann algebra, put

```text
A=tensorbar_(G/S) (A_0,tau_0),
M=A crossed_product G,                                  (ABR1)
```

and write `u_g` for the canonical group unitaries.  If

```text
F={+-I_4} <= G,                                        (ABR2)
```

then

```text
L(Gamma)' intersect M=L(F),                            (ABR3)
L(Gamma)' intersect M^omega=L(F).                      (ABR4)
```

The signs in `F` are central in `G`, belong to `S`, and hence act trivially
on `G/S`.  Consequently

```text
L(F) <= {u_h}'.                                        (ABR5)
```

Thus neither `M` nor its own tracial ultrapower contains a unitary which
centralizes `Gamma` but fails to centralize `h`.

This does **not** rule out an embedding of `M` into a larger CE algebra whose
extrinsic relative commutant grows.  It proves that such growth is now a
load-bearing part of the construction: it is absent from the canonical
amenable-orbit Bernoulli model itself.

## 2. Generalized Bernoulli actions over amenable stabilizers have spectral gap

We first isolate the general representation-theoretic input.

**Lemma 1 (amenable-orbit Bernoulli spectral gap).**  Let `Lambda` be a
nonamenable countable group acting on a countable set `Y`.  Suppose every
point stabilizer `Lambda_y` is amenable.  For a nontrivial separable finite
tracial algebra `(A_0,tau_0)`, let

```text
B=tensorbar_Y (A_0,tau_0)
```

with the generalized Bernoulli action `alpha` of `Lambda`.  Then the Koopman
representation on `L2(B) minus C1` is weakly contained in the left regular
representation of `Lambda`.  In particular it has spectral gap, and

```text
B^Lambda=C,
(B^omega)^Lambda=C.                                   (ABR6)
```

**Proof.**  Choose an orthonormal basis of `L2(A_0)` containing the constant
vector.  The corresponding finite-support tensor words form an orthonormal
basis of `L2(B)`.  Remove the constant word and decompose the remaining basis
into `Lambda`-orbits.

Let `xi` be one such tensor word and let `E` be its nonempty finite support.
The stabilizer of `xi` is contained in the setwise stabilizer of `E`.  The
latter maps to the finite permutation group of `E`; the kernel fixes every
point of `E` and is contained in

```text
intersection_(y in E) Lambda_y.
```

It is therefore amenable, and so is the stabilizer of `xi`.  The cyclic
representation carried by the orbit of `xi` is induced from a unitary
representation of this amenable stabilizer.  Every representation of an
amenable group is weakly contained in its regular representation, and
induction preserves weak containment.  Hence every orbit summand is weakly
contained in `lambda_Lambda`, and so is their direct sum.

Nonamenability of `Lambda` says that the trivial representation is not
weakly contained in `lambda_Lambda`.  Thus there are a finite set
`K subset Lambda` and `c>0` such that

```text
sum_(k in K) ||alpha_k(x)-x||_2^2
  >= c ||x||_2^2,       tau(x)=0.                      (ABR7)
```

Equation `(ABR6)` follows first for exact invariant vectors and then, by
applying `(ABR7)` coordinatewise, for invariant elements of the tracial
ultrapower.  End proof.

For `Y=G/S` the stabilizer in `Gamma` of `gS` is

```text
Gamma intersect gSg^(-1),
```

a subgroup of the amenable group `gSg^(-1)`.  Lemma 1 therefore applies to
the restriction of `(ABR1)` to `Gamma`.

## 3. Relative FC-centre of the fully framed pair

Recall the notation of the framed construction:

```text
A_ring=Z directSum J,          J^2=0,
B_+=Z[Lambda_+],               B=Z[Lambda],
R_+=B_+ directSum (B_+ tensor J),
R=B directSum (B tensor J),
Gamma=E_4(R_+),
G=E_4(R) semidirect SL_3(Z).                           (ABR8)
```

The external group acts faithfully on the Laurent exponent lattice
`Lambda`.

**Lemma 2 (exact relative FC-centre).**  An element of `G` has finite
conjugacy orbit under `Gamma` if and only if it belongs to `F={+-I_4}`.

**Proof.**  Let `x=(q,l) in G` have finite `Gamma`-conjugacy orbit.  Then
`C_Gamma(x)` has finite index in `Gamma`.  For every `i!=j`, the additive
subgroup

```text
W_ij={a in B_+ : e_ij(a) in C_Gamma(x)}                (ABR9)
```

has finite index in `B_+`: the quotient of the root subgroup by its
intersection with `C_Gamma(x)` injects into the finite coset space
`Gamma/C_Gamma(x)`.

Reduce `q` modulo the square-zero ideal `B tensor J`, writing its reduction
as `q_0 in E_4(B)`.  The commutation equation for `(ABR9)` becomes, up to
the harmless choice of semidirect-product convention,

```text
q_0^(-1) e_ij(a) q_0=e_ij(l a),       a in W_ij.       (ABR10)
```

The Laurent ring `B` is a domain.  Choosing a nonzero `a in W_ij` in
`(ABR10)` shows over `Frac(B)` that

```text
q_0^(-1) E_ij q_0=c_ij E_ij.                           (ABR11)
```

Fix nonzero `s in B_+`.  Both `W_ij` and

```text
{b in B_+ : sb in W_ij}
```

have finite additive index, so they contain a common nonzero `b`.  Apply
`(ABR10)` to `b` and `sb`, use `(ABR11)`, and cancel in the domain.  This
gives `l(s)=s`.  Since `s` was arbitrary and the external action on `B` is
faithful, `l=1`.

Equation `(ABR10)` now says that `q_0` commutes with every off-diagonal
matrix unit.  Hence `q_0` is scalar.  Its determinant is one, and the only
Laurent units whose fourth power is one are `+-1`; consequently

```text
q_0=epsilon I_4,       epsilon in {+-1}.                (ABR12)
```

Multiply by the central sign and write `epsilon q=1+Z`, where every entry
of `Z` lies in the torsion-free square-zero ideal `B tensor J`.  The element
`1+Z` still has finite `Gamma`-conjugacy orbit.  Since `(ABR9)` has finite
index, it contains `m*1` for some nonzero integer `m`.  Commutation with
`e_ij(m)` gives

```text
m[Z,E_ij]=0.
```

Torsion-freeness of `B tensor J` implies that `Z` commutes with every
matrix unit, so `Z=zI_4`.  Finally

```text
1=det(1+zI_4)=1+4z
```

because the ideal is square-zero.  Torsion-freeness again gives `z=0`.
Thus `x=epsilon I_4 in F`.  Conversely `F` is central in `G`, so every one
of its elements has a singleton `Gamma`-conjugacy orbit.  End proof.

## 4. The complete internal relative commutant

**Theorem 3.**  For the crossed product `(ABR1)`, equations `(ABR3)` and
`(ABR4)` hold.

**Proof.**  Write an element of `L2(M)` in Fourier form

```text
x=sum_(g in G) x_g u_g,       x_g in L2(A).            (ABR13)
```

If `x` is fixed by conjugation by `u_Gamma`, the norms `||x_g||_2` are
constant on the `Gamma`-conjugacy orbit of `g`.  Square summability forces
`x_g=0` on every infinite orbit.  Lemma 2 leaves only `g in F`.

The signs are central and lie in `S=C_G(h)`, so they act trivially on
`G/S` and hence on `A`.  For `g in F`, conjugation invariance of `(ABR13)`
therefore says

```text
alpha_gamma(x_g)=x_g,       gamma in Gamma.
```

Lemma 1 gives `x_g in C`.  Thus the fixed space of the conjugation
representation of `Gamma` on `L2(M)` is exactly `L2(L(F))`, proving
`(ABR3)`.

Since `Gamma` has property `(T)`, the conjugation representation has a
uniform spectral gap on the orthogonal complement of its fixed space.
Every bounded sequence in `M` which asymptotically commutes with `Gamma` is
therefore asymptotically equal in `2`-norm to its conditional expectation
onto `L(F)`.  The algebra `L(F)` is finite-dimensional, so its tracial
ultrapower is itself.  This proves `(ABR4)`.  End proof.

Because `F` is central, `(ABR5)` is immediate.

## 5. Consequence for the FALSE construction

The amenable conjugacy orbit solves two real problems:

1. its finite transition charts are sofic; and
2. the coadjoint character assigns all square-zero phases consistently.

It does not solve the commutant-wall problem.  Ordinary Bernoulli, CAR,
Clifford, matrix, or Pauli fibers over that orbit all fall under `(ABR1)`
after choosing their finite tracial base.  Their canonical crossed product
and its ultrapower satisfy

```text
u_Gamma' intersect M^omega=L(F) <= u_h'.               (ABR14)
```

Accordingly the next positive construction cannot merely decorate the
amenable orbit with independent tracial fibers.  It must produce one of:

* an **extrinsic** commutant created only after embedding the orbit algebra
  into a larger CE algebra;
* a non-Bernoulli correspondence whose `Gamma`-central sector is not the
  Koopman fixed sector; or
* directly, the one-map matrix wall from `(RBE23)--(RBE25)`.

This is a sharper target than the earlier phrase “amplify rooted visibility.”
Positive density alone is insufficient if the amplification remains an
internal generalized-Bernoulli tensor product: property `(T)` collapses its
entire asymptotic relative commutant to the harmless central signs.

