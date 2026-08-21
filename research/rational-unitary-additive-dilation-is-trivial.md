---
rg: 2
id: rational-unitary-additive-dilation-is-trivial
kind: claim
title: A rational block-unitary dilation cannot represent the additive line
distinct_from:
  central-corner-block-is-not-a-group-word: that rules out a controlled block as a word in commuting involutions; this rules out replacing characteristic-zero additive or unipotent root groups by fixed-size rational unitary matrices.
  controlled-pauli-corner-has-clifford-groupification: that positively groupifies a discrete Pauli covariance; this explains why a surviving block compiler must use such torsion/covariance data rather than rationally unitarize addition.
  unconditional-bcs-ultraproduct-decoder-forces-ce: that is a categorical obstruction from the trivial homomorphism; this is an algebraic obstruction to the proposed rational dilation itself.
---

Let `I` be an open interval about zero.  Suppose

```text
D:I -> U(n)                                                     (RAU1)
```

has entries that are rational functions of the real parameter `t`, with no
poles on `I`, and satisfies the local additive law

```text
D(s+t)=D(s)D(t)                                                 (RAU2)
```

whenever `s,t,s+t in I`.  Then

```text
D(t)=I_n  for every t in I.                                    (RAU3)
```

Thus there is no nontrivial fixed-size rational block-unitary dilation of the
elementary/unipotent rule

```text
x(a)x(b)=x(a+b).                                                (RAU4)
```

## Proof

The local group law gives `D(0)=I_n`.  Put `X=D'(0)`.  Differentiating
`D(t+h)=D(t)D(h)` at `h=0` gives

```text
D'(t)=D(t)X.                                                    (RAU5)
```

Hence on `I`,

```text
D(t)=exp(tX).                                                   (RAU6)
```

Unitarity for real `t` implies `X*=-X`.  Every entry of the rational matrix
`D(t)` agrees near zero with the corresponding entire entry of `exp(tX)`.
By analytic continuation, every finite pole of that rational function is
removable.  Therefore each entry is an entire rational function, hence a
polynomial.  But every entry of `D(t)` is bounded by one on the real axis,
so each polynomial is constant.  Since `D(0)=I_n`, `(RAU3)` follows.

Equivalently, an algebraic/rational homomorphism from the characteristic-zero
additive group into a compact unitary group is trivial.

## Compiler consequence

A common proposed lowering first encodes star-algebra addition by elementary
unipotents and then replaces each unipotent by a rational unitary dilation on
a fixed ancillary block.  If the dilation is required to preserve the
additive multiplication table exactly, `(RAU1)--(RAU4)` show that all of the
encoded coefficients collapse.

This does not rule out every block-unitary groupifier.  It leaves three
genuinely different possibilities:

- use a non-rational exponential/functional-calculus encoding, while finding
  separate recursively enumerable group relations that force its analytic
  semantics;
- work with discrete finite-characteristic/torsion packets such as Pauli
  root groups; or
- use block unitaries only for covariance and recover addition from another
  matrix-coordinate theorem.

The first option is not a rational group-presentation compiler, and the
second and third retain the existing nonlinear incidence/marked-corner
problem.  Rational dilation alone therefore does not bypass the BCS
groupification frontier.
