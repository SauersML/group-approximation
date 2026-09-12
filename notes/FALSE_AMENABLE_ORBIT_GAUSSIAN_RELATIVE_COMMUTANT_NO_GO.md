# Gaussian and free-Gaussian fibers over the amenable orbit still have no wall

Date: 2026-08-12

## 1. Outcome

Let `Gamma<G`, let `h in G`, and put

```text
S=C_G(h),       Y=G/S.
```

For the fully framed pair in
`FALSE_FULLY_FRAMED_AMENABLE_CONJUGACY_ORBIT.md`, the group `S` is
amenable, `Gamma` is a nonamenable property-`(T)` group, and the relative
FC-centre is

```text
FC_G(Gamma)={g in G:|{gamma g gamma^(-1):gamma in Gamma}|<infinity}
           ={+-I_4}=:F.                                (GNR1)
```

The amenability of `S` suggests replacing the independent Bernoulli fibers
ruled out in
`FALSE_AMENABLE_ORBIT_BERNOULLI_RELATIVE_COMMUTANT_NO_GO.md` by the
classical Gaussian or free Gaussian functor applied to the quasi-regular
orthogonal representation

```text
rho:G->O(ell^2_R(Y)).                                  (GNR2)
```

This note proves that the replacement does not help.  If `A_rho` is either
the classical Gaussian algebra or the free Gaussian algebra and

```text
M=A_rho crossed_product G,                             (GNR3)
```

then

```text
L(Gamma)' intersect M=L(F),
L(Gamma)' intersect M^omega=L(F) <= {u_h}'.            (GNR4)
```

Thus neither symmetric Fock space nor full Fock space produces the required
`Gamma`-central unitary.  The obstruction is not tensor independence.  It is
weak regularity of the entire nonconstant Fock representation after
restriction to `Gamma`.

## 2. Weak regularity survives every Fock chaos

We use the following standard weak-containment calculation in a form that
also covers finite-index subgroups.

**Lemma 1 (Fock spectral gap).**  Let `Lambda` be a nonamenable countable
group and let

```text
pi:Lambda->O(H_R)
```

be weakly contained in a multiple of the real regular representation.  Let
`A_pi` be either its classical Gaussian algebra or its free Gaussian
algebra.  Then the Koopman representation on

```text
L2(A_pi) minus C1                                      (GNR5)
```

is weakly contained in a multiple of `lambda_Lambda`.  In particular

```text
A_pi^Lambda=C.                                         (GNR6)
```

If `Lambda` has property `(T)`, then also

```text
(A_pi^omega)^Lambda=C.                                 (GNR7)
```

**Proof.**  After complexification, the nonconstant part of the classical
Gaussian Koopman representation is contained in the symmetric Fock sum

```text
directSum_(n>=1) Sym^n(pi_C),                          (GNR8)
```

whereas for the free Gaussian functor it is the full Fock sum

```text
directSum_(n>=1) pi_C^(tensor n).                      (GNR9)
```

Weak containment is preserved by tensoring.  Fell absorption gives

```text
lambda_Lambda tensor sigma
  ~= multiple of lambda_Lambda                         (GNR10)
```

for every unitary representation `sigma`.  Starting with
`pi_C weakly_contained lambda_Lambda`, induction using `(GNR10)` shows that
every tensor power in `(GNR9)` is weakly regular.  The symmetric powers in
`(GNR8)` are subrepresentations of the corresponding tensor powers.  Direct
sums preserve weak containment, proving the first assertion.

Nonamenability says that the trivial representation is not weakly
contained in `lambda_Lambda`; hence `(GNR5)` has no invariant vector and
`(GNR6)` follows.  If `Lambda` has property `(T)`, a Kazhdan pair gives a
uniform gap on the orthogonal complement of the invariant vectors.  Applying
that inequality coordinatewise to a bounded representing sequence proves
`(GNR7)`.  End proof.

The same conclusion applies to every finite-index subgroup of `Lambda`:
finite-index subgroups of a nonamenable property-`(T)` group are again
nonamenable and have property `(T)`.

## 3. The amenable stabilizer makes the quasi-regular representation weakly regular

**Lemma 2.**  For `(GNR2)`, the restriction of `rho` to every finite-index
subgroup `Gamma_0<=Gamma` is weakly contained in a multiple of
`lambda_(Gamma_0)`.

**Proof.**  The quasi-regular representation in `(GNR2)` is

```text
Ind_S^G(1_S).
```

Since `S` is amenable, `1_S` is weakly contained in `lambda_S`.  Induction
preserves weak containment, and induction of `lambda_S` is `lambda_G`.
Therefore

```text
rho weakly_contained lambda_G.                         (GNR11)
```

Restriction preserves weak containment.  The restriction of `lambda_G` to
`Gamma_0` is a multiple of `lambda_(Gamma_0)`, proving the claim.  End
proof.

Combining Lemmas 1 and 2 gives

```text
A_rho^(Gamma_0)=C                                      (GNR12)
```

for every finite-index `Gamma_0<=Gamma`, as well as the corresponding
ultrapower statement when `Gamma_0=Gamma`.

There is also a useful conceptual converse hidden here.  A representation
weakly contained in `lambda_G` cannot contain a nonzero `Gamma`-fixed vector
when `Gamma` is nonamenable: restriction would weakly contain the trivial
representation in a multiple of `lambda_Gamma`.  Thus no weak-regularity
permanence theorem can simultaneously supply the fixed anchor required by
the relative-commutant endpoint.

## 4. General relative-commutant calculation

The Fock calculation feeds into a crossed-product lemma which is independent
of Gaussianity.

**Lemma 3 (relative FC support).**  Let a property-`(T)` group `Lambda<G`
act trace preservingly on a finite algebra `(A,tau)`.  Suppose

```text
A^(Lambda_0)=C                                         (GNR13)
```

for every finite-index subgroup `Lambda_0<=Lambda`.  Put `N=A crossed G`.
Then

```text
L(Lambda)' intersect N <= L(FC_G(Lambda)).             (GNR14)
```

If, in addition,

```text
FC_G(Lambda)<=C_G(Lambda)                              (GNR14a)
```

and its elements act trivially on `A`, equality holds in `(GNR14)`.  If
this relative FC-centre is finite, then the same equality holds in
`N^omega`.

**Proof.**  Write a vector of `L2(N)` in Fourier form

```text
x=sum_(g in G) a_g u_g.
```

Commutation with `u_Lambda` gives

```text
a_(lambda g lambda^(-1))=sigma_lambda(a_g).            (GNR15)
```

The coefficient norms are constant on each `Lambda`-conjugacy orbit.
Square summability therefore kills every infinite orbit.  If the orbit of
`g` is finite, its stabilizer is `C_Lambda(g)`, a finite-index subgroup of
`Lambda`, and `(GNR15)` says

```text
a_g in A^(C_Lambda(g))=C.                              (GNR16)
```

This proves `(GNR14)`.  Under `(GNR14a)`, if every relative-FC element acts
trivially, scalar Fourier series supported there do commute with
`L(Lambda)`, proving equality.

Finally property `(T)` gives a uniform spectral gap for the conjugation
representation on the orthogonal complement of its fixed space.  Hence an
asymptotically central bounded sequence is asymptotically equal to its
conditional expectation onto the fixed algebra.  When the relative
FC-centre is finite, that algebra is finite dimensional and its tracial
ultrapower is itself.  End proof.

## 5. Application to the fully framed pair

Apply Lemma 3 with `Lambda=Gamma` and `A=A_rho`.  Equation `(GNR12)` gives
its fixed-point hypothesis.  The exact relative FC-centre calculation
`(GNR1)` was proved in
`FALSE_AMENABLE_ORBIT_BERNOULLI_RELATIVE_COMMUTANT_NO_GO.md`.

The signs in `F` are central in `G` and lie in `S`.  They therefore act
trivially on `G/S`, hence trivially in both Gaussian functors.  Lemma 3 now
gives both equalities in `(GNR4)`.  Centrality of `F` gives the final
inclusion in `{u_h}'`.

The result closes the most plausible analytic use of the amenable
conjugacy stabilizer.  Any surviving construction must abandon at least one
of the following:

1. a functor whose nonconstant `Gamma`-representation is weakly regular;
2. an internal crossed-product commutant; or
3. the amenable-stabilizer orbit as the only source of fiber labels.

An extrinsic commutant inside a larger CE algebra, or a genuinely
nonliftable finite correspondence not generated by the Fock functor, remains
possible.
