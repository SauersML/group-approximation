---
rg: 2
id: fanizza-c18-residual-factors-through-three-tiny-rank-gates
kind: claim
title: Fanizza C18 residuals factor through three tiny child-guarded parity gates
artifacts:
  - experiments/fanizza_factored_c18_exit_compiler.py
distinct_from:
  c18-child-oriented-gates-follow-the-two-source-words: that compiles two six-variable predicates with matrix sizes 9 and 10; this factors the phase parity first and reduces the gates to sizes 5, 5, and 6.
  c18-source-cut-has-sparse-relator-certificate: that transfers the aggregate source-local forbidden mass on approximate shared words; this gives the exact finite packets that consume the transferred mass.
---

Let `h` be the even-parity bit of C18's last three selectors.  The positive
integer residual occurrence count has the pointwise factorization

```text
e_1+e_2
 = h p(1-r) + h q(1-r) + h p q r.                    (FCR1)
```

The first gate is attached to the literal `p` recurrence child, the second
and third to the literal `q` child.  The last-three-variable dependence is
only the affine bit

```text
h=1+x_3+x_4+x_5  over F_2.                             (FCR2)
```

Compile the first two predicates on compressed variables `(child,r,h)` and
the third on `(p,q,r,h)`, then substitute `(FCR2)` into the affine Schur
matrix.  The optimized baseline ranks are `4,4,5`, with matrix sizes

```text
5, 5, 6.                                               (FCR3)
```

All 20 original six-bit occurrences admit source-fixed weight-two frames
with the same symmetric kernel, the single hard root `e_02^*`, and one fixed
left/right word pair for each of the three gates.  Thus the phase's four
Boolean atoms require no atom-dependent packet chart: they are four lifts of
one compressed affine character.

This is the smallest current C18 interface.  It replaces the size-11/10
oriented packets and the size-9/10 child-oriented packets without changing
the scalar active/exit ledger or the source-cut certificate.
