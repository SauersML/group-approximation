---
rg: 2
id: leavitt-two-compressor-core-is-lef-and-marked-operator-mf
kind: claim
title: The elementary two-compressor core is LEF and its marked lamp is operator-MF visible
artifacts:
  - research/leavitt-two-compressor-modular-lef-proof.md
distinct_from:
  leavitt-el20-two-compressor-fd-representations-kill-mark: that proves every single exact finite-dimensional representation kills the diagonal lamp group; LEF supplies a sequence of exact finite partial models, not one exact representation of the whole group.
  leavitt-two-compressor-covariance-triangle-has-marked-models: that models only the depth-one covariance table and misses a literal depth-two relation; this models every prescribed finite multiplication table of the actual semidirect product.
  leavitt-st20-two-compressor-mark-is-mf-invisible: that is an open claim about chosen Steinberg lifts; this proves the opposite conclusion for the downstairs elementary core after using its exact split normal form.
---

Let `H=GL_5(F_2)`, let `X={0,1}^N`, and let

```text
B_EL = C_lc(X,H) semidirect (C_2*C_3)
```

be the exact elementary two-compressor normal form.  Then `B_EL` is locally
embeddable into finite groups.  Consequently `B_EL` is operator-MF and

```text
Rad_MF(B_EL)=1.
```

In particular the nontrivial marked diagonal root is retained by an
operator-norm matrix-corona representation.

The LEF construction is intrinsic.  For a prescribed finite multiplication
table, retain the finitely many intermediate translates of its lamp
coefficients.  The involutory and cubic actor generators separately preserve
finite refinements of the resulting clopen algebra.  Their two finite
semidirect products amalgamate over the original finite lamp group.  This is
a finite graph of finite groups, so a finite quotient of it realizes the
prescribed table exactly.

Thus the literal recursive child-splitting relations missing from the
`H x H` covariance model do not create an MF obstruction downstairs.  They
are instead captured by finite graph-of-finite-groups models whose finite
quotient is allowed to depend on the requested multiplication table.

DERIVATION
leavitt-two-compressor-modular-lef-proof
