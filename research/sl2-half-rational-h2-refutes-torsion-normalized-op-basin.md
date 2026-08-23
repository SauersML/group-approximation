---
rg: 2
id: sl2-half-rational-h2-refutes-torsion-normalized-op-basin
kind: claim
title: Rational H2 refutes a global operator-norm basin after Iwahori torsion normalization
distinct_from:
  invariant-bs-block-cut-leaves-a-passive-coordinate-basin: that asks for a flexible basin after the BS core and inversion have already been made exact and an active sublinear block has been removed; this proves that the tempting alternative normalization, which makes the torsion frame exact, cannot have a global strict operator-norm basin.
  iwahori-two-triangle-torsion-normal-form: that gives the same-dimensional spectral normalization in normalized Hilbert--Schmidt norm; the identical scalar inequalities work in operator norm, and this claim records the global obstruction which survives that normalization.
  iwahori-uniform-infinitesimal-rigidity: that proves a uniform derivative gap inside an existing congruence tube; this proves that exact torsion plus that local gap cannot manufacture the tube globally.
  dadarlat-matricial-stability-obstruction: that records the external theorem and its hypotheses; this computes the required rational cohomology for the particular arithmetic group and transports the obstruction through the explicit torsion normalization.
---

**ESTABLISHED STRICT FIREWALL.**  Put

```text
G=PSL_2(Z[1/2]).
```

Then

```text
H^2(G,Q) ~= Q.                                             (RHB1)
```

Consequently `G` is not matricially stable in operator norm.  Moreover,
after applying nearest-root functional calculus to an arbitrary
operator-norm asymptotic representation, all three Iwahori torsion rows can
be made exact by an operator-norm perturbation tending to zero.  Therefore
there is a sequence of exact torsion frames whose two remaining structural
defects tend to zero in operator norm but which does not approach the exact
Iwahori representation variety in operator norm.

In particular, exact order two/order three normalization plus the uniform
Selberg tangent gap does **not** imply operator-norm proximity to the union
of congruence endpoints.  The tangent gap remains a local theorem.

## Rational cohomology computation

The one-edge Bruhat--Tits quotient gives the standard amalgam

```text
G = PSL_2(Z) *_(Gamma_0(2)) PSL_2(Z),                      (RHB2)
```

with the second vertex conjugated by the determinant-two diagonal element.
As abstract groups,

```text
PSL_2(Z) ~= C_2*C_3,
Gamma_0(2) ~= C_2*Z.                                      (RHB3)
```

Hence both vertex groups and the edge group are virtually free,

```text
H_2(PSL_2(Z),Q)=0,
H_1(PSL_2(Z),Q)=0,
H_1(Gamma_0(2),Q)=Q.                                     (RHB4)
```

The Mayer--Vietoris sequence for `(RHB2)` contains

```text
0 -> H_2(G,Q) -> H_1(Gamma_0(2),Q)
  -> H_1(PSL_2(Z),Q) (+) H_1(PSL_2(Z),Q) -> 0.
```

Using `(RHB4)` gives `H_2(G,Q)=Q`.  The universal coefficient theorem over
the field `Q` proves `(RHB1)`.

## Operator-norm obstruction and normalization

The group `G` is countable and linear.  Dadarlat's Corollary 1.3, as
recorded with its exact hypotheses in
`dadarlat-matricial-stability-obstruction`, says that a countable linear
group with nonzero rational even cohomology is not weakly matricially
stable.  In particular it is not matricially stable.  Thus there are
finite-dimensional unitary asymptotic homomorphisms of `G` which cannot be
perturbed pointwise in operator norm to genuine same-dimensional
representations.

Write one such sequence in the square-free Iwahori coordinates `(X,R,T)`.
The proof of `iwahori-two-triangle-torsion-normal-form` is norm-independent:
for a unitary `V`, nearest-cube-root functional calculus gives

```text
||V-V_0||_op <= (1/2)||V^3-1||_op,       V_0^3=1,       (RHB5)
```

and nearest-sign rounding gives

```text
||X-X_0||_op <= ||X^2-1||_op,            X_0^2=1.       (RHB6)
```

The same substitutions and fixed-word telescoping therefore produce a new
sequence, at operator-norm distance tending to zero from the old one, with

```text
X^2=(XT)^3=(XT^2R)^3=1                                  (RHB7)
```

exactly, while the inversion and BS covariance defects still tend to zero
in operator norm.  If every tuple satisfying `(RHB7)` and having small two
structural defects were operator-norm close to an exact representation,
the triangle inequality would correct the original asymptotic
homomorphism.  This contradicts matricial instability.

## Exact limit of the conclusion

This result does **not** refute
`invariant-bs-block-cut-leaves-a-passive-coordinate-basin`.  That claim
starts in the opposite normal form: the entire BS core and inversion row
are exact, only the two cubics are small, and flexible `o(d)` repair is
allowed after an active block cut.  Dadarlat's strict countersequence is not
known to survive an operator-norm exactification of the BS core, and
non-weak matricial stability is formulated using stabilized ucp maps rather
than supplying the required relative unitary countersequence.

What is refuted is the proposed shortcut

```text
exactify torsion
  + invoke the uniform tangent gap
  => enter the global congruence coordinate basin.
```

The arithmetic route must retain the exact-BS/passive hypothesis and prove
a genuinely **relative flexible** lifting theorem there.  Switching to the
exact-torsion normal form loses precisely the extra structure capable of
evading the rational `H^2` obstruction.
