---
rg: 2
id: odd-retract-positive-kernel-proof
kind: route
title: Apply Schwarz twice and then use finite-dimensional invisibility
target: odd-maslov-ucp-retract-must-hide-generator-defect
requires:
  - deligne-triple-cover-fd-central-invisibility
  - metaplectic-half-class-has-an-exact-finite-model
  - maslov-mod3-gap-is-metaplectic-base-degree-six-gap
---

Since `i` is ucp and `u_s` is unitary, Schwarz gives

```text
i(u_s)^*i(u_s) <= 1,        i(u_s)i(u_s)^* <= 1.
```

Thus `d_s^L,d_s^R` are positive.  Apply `r`.  Schwarz for `r` and
`r(i(u_s))=u_s` give

```text
1 = u_s^*u_s
  = r(i(u_s))^*r(i(u_s))
 <= r(i(u_s)^*i(u_s))
 <= r(1)=1.
```

Both inequalities are equalities, hence `r(d_s^L)=0`; the right-hand version
is identical.  This proves `(OUR2)`.

If all defects vanish, each `i(u_s)` is unitary.  Equality in both Schwarz
inequalities puts every `u_s` in the multiplicative domain of `i`.  The
canonical projective generators generate `A_alpha`, so `i` is a unital
star-homomorphism.  The even target has a nonzero finite-dimensional
representation: for `epsilon=0` use the trivial character, and for
`epsilon=1/2` use `metaplectic-half-class-has-an-exact-finite-model`.
Composing its matrix amplification with `i` gives a nonzero
finite-dimensional representation of `A_alpha`.

For `alpha=1/3` or `2/3`, that contradicts
`deligne-triple-cover-fd-central-invisibility`.  For `alpha=1/6` or `5/6`,
it gives a finite-dimensional representation of `E_6` nontrivial on the
full finite residual `Z/3` from
`maslov-mod3-gap-is-metaplectic-base-degree-six-gap`, again impossible.
Therefore at least one defect in `(OUR2)` is a nonzero positive element.
Faithfulness of `r` is impossible.

If every generator image is unitary, the preceding multiplicative-domain
argument applies directly.  A unital completely positive order-zero map is
a star-homomorphism, so it is also impossible.  Finally a conditional
expectation onto a star-subalgebra inclusion starts with a star-homomorphic
`i`, already ruled out (and if the expectation is faithful, it is also ruled
out directly by `(OUR2)`).

