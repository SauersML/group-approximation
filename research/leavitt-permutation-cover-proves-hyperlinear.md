---
rg: 2
id: leavitt-permutation-cover-proves-hyperlinear
kind: route
title: A permutation regular-atlas cover gives a sofic central extension and a hyperlinear nonsofic Leavitt quotient
target: binary-leavitt-unit-group-hyperlinear
requires:
  - leavitt-regular-atlas-asymptotic-permutation-cover
  - leavitt-regular-atlas-hyperlinearity-criterion
  - thom-central-corner-criterion
---

Assume `(APC1)--(APC2)`.  The permutation ultraproduct gives a homomorphism

```text
Phi:U_Q=bar P/bar N -> product_omega Sym(Omega_n).       (PCP1)
```

It is nontrivial: every nonidentity element of the first `A_8` factor moves
every point of `Omega_n`, so its image has Hamming distance one from the
identity.  Quasisimplicity of `U_Q`, already used in
`leavitt-regular-atlas-hyperlinearity-criterion`, therefore gives

```text
ker(Phi) <= Z(U_Q).                                     (PCP2)
```

Put `W=Phi(U_Q)`.  As a subgroup of a permutation ultraproduct, `W` is
sofic, hence hyperlinear.  Equation `(PCP2)` makes it a central extension

```text
1 -> Z(U_Q)/ker(Phi) -> W -> Q -> 1.                    (PCP3)
```

Thom's central-quotient theorem (`thom-central-corner-criterion`) says that
a central quotient of a hyperlinear group is hyperlinear.  Applying it to
`(PCP3)` proves that the binary Leavitt unit group `Q` is hyperlinear.
Together with `openai-leavitt-unit-nonsofic`, this is the desired
hyperlinear/nonsofic separation.

There is deliberately no assertion that `Q` is sofic.  Soficity does not
have the central-quotient permanence used in the last paragraph; confusing
the two would incorrectly turn the established nonsoficity of `Q` into an
obstruction to `(APC1)--(APC2)`.  In fact that failure of sofic descent is
exactly why the permutation-cover target is a viable positive route.

Finally, a permutation relative chart unitary is a special case of the
unitary in the regular-atlas criterion, and

```text
||P-I||_2^2 = 2 d_H(P,1)
```

for permutation matrices.  Thus `(APC2)` also feeds the criterion directly;
the central-extension argument above explains the group-theoretic content of
that specialization.
