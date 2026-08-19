# Automorphic isolation does not capture the Iwahori basin

Date: 2026-08-14

## 1. Outcome

An automorphic spectral-gap theorem for the congruence representations of

```text
G=SL_2(Z[1/2])=K *_(B_+ ~= B_-) K,       K=SL_2(Z),   (AGB1)
```

would be useful, but it cannot by itself answer the Dogon--Vigdorovich
matching question.

The reason is logical rather than quantitative.  Automorphic isolation is a
statement at **honest compatible representations** of `G`.  It can supply a
uniform local inverse estimate for the linearized restriction map there.
Question 1.4 starts with two arbitrary finite-dimensional representations of
`K` whose Iwahori restrictions are close.  These vertex representations need
not have finite image and need not be close to a compatible representation.
Small edge defect produces an exact representation of `G` only after passing
to a tracial matrix ultraproduct.

Therefore a complete proof has two independent parts:

```text
uniform local repair at the compatible locus, and
uniform basin capture for every small-defect vertex pair.              (AGB2)
```

Congruence automorphic isolation addresses, at most, the first line.  The
second line is a coordinate-lifting or regular-microstate-uniqueness theorem.
It cannot be omitted from a Newton argument.

This note gives the exact local-to-global criterion and corrects the prior
temptation to treat a cohomological automorphic gap as the last theorem.

## 2. Defect and distance

For a matrix dimension `d`, let `X_d` be the pairs

```text
x=(alpha,beta),       alpha,beta:K->U(d),              (AGB3)
```

where both vertex maps are honest representations.  Let `Z_d subset X_d` be
the compatible pairs, equivalently the restrictions of representations
`G->U(d)`.  Write

```text
epsilon_d(x)=def(x),
D_d(x)=dist_2(x,Z_d).                                  (AGB4)
```

One may replace `D_d` by the flexible metric allowing negligible padding.
The distinction does not affect the logical separation below.

There are two different uniform assertions.

**Local inverse estimate.**  There are `r,C>0`, independent of `d`, such
that

```text
D_d(x)<r       implies       D_d(x)<=C epsilon_d(x).    (AGB5)
```

**Basin capture.**  There is `delta_0>0`, independent of `d`, such that

```text
epsilon_d(x)<delta_0       implies       D_d(x)<r.       (AGB6)
```

Together `(AGB5)--(AGB6)` give the desired uniform estimate

```text
D_d(x)<=C epsilon_d(x)                                 (AGB7)
```

for all sufficiently small defects.  More generally, if basin capture gives
`D_d(x)<=b(epsilon_d(x))` for a function `b(delta)->0`, a local Newton
estimate supplies a global stability modulus.

The converse separation is just as important.  A positive answer to
Question 1.4 immediately implies `(AGB6)` for every fixed `r>0`.  Thus basin
capture is not a harmless compactness detail: it contains the qualitative
global stability assertion.

## 3. A local gap never implies basin capture formally

Even a perfect, dimension-independent derivative bound near every zero does
not exclude almost zeros far from the zero set.  The scalar family

```text
X_n=R,       Z_n={0},       f_n(x)=|x|/(1+x^2)          (AGB8)
```

has a uniform local inverse estimate near `0`: for `|x|<=1`,

```text
|x|<=2 f_n(x).                                         (AGB9)
```

But at `x=n`,

```text
f_n(n)->0,       dist(n,Z_n)=n.                        (AGB10)
```

This elementary model is not offered as a group-theoretic counterexample.
It isolates the invalid inference: uniform transversality at the exact locus
does not prevent a high-dimensional escape component on which the defining
relations become small.

For each fixed `d`, compactness of `X_d` rules out such an escape at that
dimension.  Question 1.4 asks for a modulus uniform in `d`; the compactness
constants may degenerate as the dimension and irreducible type grow.  The
fixed-type theorem in
`TRUE_IWAHORI_MATCHING_FIXED_TYPE_REDUCTION.md` proves basin capture on each
fixed finite representation library, and also shows exactly why this does
not give a uniform unrestricted modulus.

## 4. What congruence theory actually controls

Dogon--Vigdorovich use the congruence subgroup property of `G` to identify
honest finite-dimensional representations of `G`: their restrictions to a
modular vertex factor through odd congruence quotients.  In the notation
above, this describes the points of `Z_d`.

It does **not** say that every point of `X_d` factors through a congruence
quotient.  Indeed, `K=SL_2(Z)` is virtually free and has continuous families
of finite-dimensional unitary representations with infinite image.  The
claim that a small-defect point of `X_d` is close to an odd-congruence point
is the conclusion of Question 1.4, not an available reduction before basin
capture has been proved.

At a point `rho in Z_d`, the linearized mismatch map is the Bass--Serre
restriction difference

```text
R_(Ad rho):
H^1(K,Ad rho) directSum H^1(K,Ad rho)
   -> H^1(B_+,Ad rho).                                 (AGB11)
```

A uniform lower bound on the positive singular values of `(AGB11)` is a
genuine and potentially automorphic local theorem.  Since `rho` is an honest
representation of `G`, congruence methods are in scope at this point.  The
large cokernel identified in
`TRUE_IWAHORI_FACTOR_GATE_IS_COSYSTOLIC_ANGLE.md` is compatible with such a
positive gap; one must quotient by the exact kernel and allow harmonic
degree-two modes.

Even granting the strongest possible positive singular-value bound for
every congruence `rho`, `(AGB11)` is defined only after a nearby base point
`rho` has been supplied.  It cannot manufacture that base point from an
arbitrary small-defect pair.

## 5. The ultraproduct form of the missing theorem

Suppose basin capture fails.  Then for some `r>0` there are dimensions
`d_n` and exact modular vertex pairs `x_n in X_(d_n)` such that

```text
epsilon_(d_n)(x_n)->0,
D_(d_n)(x_n)>=r.                                      (AGB12)
```

The vanishing edge discrepancy means that the two vertex representations
agree on the Iwahori subgroup in the tracial matrix ultraproduct.  Hence they
glue there to an exact homomorphism

```text
Pi:G->U(product_omega M_(d_n)).                        (AGB13)
```

But `(AGB12)` says precisely that `Pi` has no coordinate representatives by
honest finite-dimensional representations of `G` within the prescribed
radius, even after the permitted negligible padding.  Therefore `(AGB6)` is
a lifting theorem for the special ultraproduct homomorphisms whose two
modular vertex restrictions lift exactly.

The limiting trace of `(AGB13)` does not determine this lifting question.
Character rigidity reduces a negative sequence to a central-regular trace,
and residual finiteness supplies congruence representations with the same
limiting trace.  What is missing is a unitary matching of the two matrix
models, not the existence of some model with the same character.  Equality
of traces in the limit is weaker than coordinate conjugacy or liftability.

Thus the remaining global assertion may be stated as follows.

> **Regular-sector Iwahori basin theorem.**  Every tracial-ultraproduct
> representation `(AGB13)` with central-regular trace and with exactly
> liftable modular vertex restrictions admits, after negligible padding, a
> lift by compatible finite-dimensional representations of `G`.

This is the global companion to the local cosystolic-angle theorem.

## 6. Corrected proof architecture

A valid completion of the Iwahori program now has four gates.

1. **Basin capture.**  Prove `(AGB6)`, or the stronger regular-sector
   ultraproduct lifting theorem above.
2. **Local cosystolic gap.**  Prove a dimension-independent positive
   singular-value bound for `(AGB11)` on the complement of its kernel.
3. **Harmonic integrability.**  Show that the factorized `BS(1,4)` correction
   has quadratic, rather than linear, component in the cokernel
   `H^2(G,Ad rho)`.
4. **Uniform retraction.**  Control the nonlinear modular representation
   strata with dimension-independent quadratic remainder.

Gate 1 enters the Newton neighborhood.  Gates 2--4 keep the Newton iteration
there and make it converge.  No combination of Gates 2--4 alone proves Gate
1.

The immediate research consequence is that automorphic isolation should be
studied as a possible proof of Gate 2, not advertised as a route to the full
matching theorem.  The main global target remains regular-sector microstate
uniqueness for the Iwahori amalgam.

## 7. Status

The local-to-global separation `(AGB5)--(AGB7)`, the scalar countermodel
`(AGB8)--(AGB10)`, the scope of the congruence classification, and the
ultraproduct construction `(AGB12)--(AGB13)` are exact.

Neither the regular-sector basin theorem nor the local cosystolic Newton
theorem is proved here.  This note prevents a false proof in which an
automorphic spectral gap is silently used to place an arbitrary almost
representation near the congruence locus.

## References

- M. Dogon and I. Vigdorovich, *Hyperlinearity, stability and asymptotic
  spectral gap of higher rank lattices*,
  [arXiv:2506.20843v2](https://arxiv.org/abs/2506.20843v2), especially
  Question 1.4 and the congruence reformulation immediately following it.
- N. Bergeron, *Representations cohomologiques isolees, applications
  cohomologiques*,
  [arXiv:math/0511689](https://arxiv.org/abs/math/0511689), for the scope and
  limitations of automorphic isolation of cohomological representations.
