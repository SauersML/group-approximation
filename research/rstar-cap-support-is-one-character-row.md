---
rg: 2
id: rstar-cap-support-is-one-character-row
kind: claim
title: Fano-cap support is exactly one fixed nontrivial character row per context
distinct_from:
  rstar-fano-caps-have-seven-maximal-parity-covers: that classifies the seven maximal caps as subsets of the Fano plane; this identifies the corresponding operator identity and exact LCS quotient interface for representations.
  rstar-fano-cap-support-preserves-nonru-affine-relaxation: that proves soundness after a cap-supported affine relaxation is chosen; this says exactly which one-row quotient a cap-supported representation satisfies.
  culf-mastel-rstar-halt-model-has-fano-cap-support: that asks for existence of the special HALT representation; this is the unconditional local equivalence used to state that open gate as seven character choices.
---

**ESTABLISHED.**  Let one perfect `R_*` context be represented in its finite
von Neumann algebra with faithful trace by commuting self-adjoint involutions
`X_1,X_2,X_3,X_4`, with joint atom `x` carrying eigenvalues
`(-1)^(x_j)`.  For nonzero
`a=(a_2,a_3,a_4) in F_2^3`, put

```text
Y_a=X_2^(a_2) X_3^(a_3) X_4^(a_4).                    (FCH1)
```

For the positive joint spectral support `S`, the following are equivalent:

```text
S+g is a Fano cap;
S subseteq {x in R_*:a_2 x_2+a_3 x_3+a_4 x_4=1}
  for some a != 0;
Y_a=-I for some a != 0.                                 (FCH2)
```

Consequently, if a finite `R_*` instance has nonlinear contexts
`c=1,...,m`, a perfect representation is cap-supported at every context if
and only if it satisfies one character profile

```text
alpha=(a_c)_c in (F_2^3\{0})^m,                         (FCH3)
```

or equivalently factors through one of exactly `7^m` affine LCS quotients.
The quotient for context `c` keeps the original row

```text
x_(c,1)+x_(c,2)+x_(c,3)+x_(c,4)=1                     (FCH4)
```

and adds only

```text
a_(c,2)x_(c,2)+a_(c,3)x_(c,3)+a_(c,4)x_(c,4)=1.        (FCH5)
```

The added row excludes the ghost because its last three coordinates vanish.
Thus every solution of the quotient still satisfies the original `R_*`
predicate.  This is an exact representation-theoretic equivalence, not a
selection theorem: it does not prove that a HALT model satisfying one of the
profiles exists.
