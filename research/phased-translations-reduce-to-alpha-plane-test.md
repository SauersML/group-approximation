---
rg: 2
id: phased-translations-reduce-to-alpha-plane-test
kind: claim
title: Phased translations reduce primitive two-matching stability to one affine-orbit test
distinct_from:
  full-weyl-defect-equals-pvm-transport-energy: that is an operator-valued Parseval identity for an arbitrary common PVM; this is the scalar diagonal-conjugacy family that could have supplied a finite-dimensional counterrepresentation.
  two-field-matchings-rigidify-linear-weyl-mislabels: that treats linear Weyl label changes; the Boolean phase here is completely arbitrary and may have every algebraic degree.
---

ESTABLISHED.  Let `K=F_(2^n)`, let `alpha` generate `K` over `F_2`, and
write `T_a e_x=e_(x+a)` on `H=ell^2(K)`.  For an arbitrary Boolean function
`P:K->F_2`, put

```text
R_P e_x=(-1)^P(x) e_x,
X(a)=T_a,                    Z(b)=R_P T_b R_P.                (PT1)
```

Both tables are exact additive representations.  A direct calculation on
`e_x` gives

```text
X(a)Z(b)e_x
 =(-1)^(Delta_a Delta_b P(x)) Z(b)X(a)e_x.                   (PT2)
```

Consequently the identity matching is exact, while normalized Hilbert--Schmidt
defects are exactly Boolean rejection probabilities:

```text
E_b ||X(alpha b)Z(b)-Z(b)X(alpha b)||_2^2
 =4 Pr_(x,b)[Delta_b Delta_(alpha b) P(x)=1],                (PT3)

E_(a,b) ||X(a)Z(b)-Z(b)X(a)||_2^2
 =4 Pr_(x,a,b)[Delta_a Delta_b P(x)=1].                      (PT4)
```

Thus any scalar/monomial counterexample to uniform stability in this family
would be precisely a sequence of Boolean functions for which the four-point
`alpha`-plane test has rejection tending to zero but the ordinary
parallelogram test has rejection bounded away from zero.

No such counterexample exists.  In fact, if `r_alpha(P)` and `r_all(P)` denote
the probabilities in `(PT3)` and `(PT4)`, then

```text
r_all(P) <= (27/2) r_alpha(P),                               (PT5)

E_(a,b)||X(a)Z(b)-Z(b)X(a)||_2^2
 <=(27/2) E_b||X(alpha b)Z(b)-Z(b)X(alpha b)||_2^2.           (PT6)
```

The proof is `alpha-plane-single-orbit-soundness-proof`.  Its important scope
is negative as well as positive: primitive multiplication has no uniform
spectral gap on `K^*`, but slow variation around that multiplicative cycle
does not integrate to a bad Boolean phase.  The remaining robust problem is
genuinely operator-valued/noncommutative; a counterexample cannot come merely
from conjugating translations by one diagonal sign matrix.
