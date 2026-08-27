---
rg: 2
id: q-masa-expectation-erases-predicate-shape-proof
kind: route
title: Truncate the selector Fourier expansion to the q-MASA support
target: q-masa-expectation-erases-predicate-shape
requires:
  - full-q-masa-forgets-selectors-retains-branches
  - schur-predicate-is-character-density-difference
---

Distinct group elements are linearly independent in the ambient group
algebra. Therefore, for any subgroups `H,L` of a group,

```text
C[H] intersect C[L]=C[H intersect L].                    (QEP1)
```

Apply this to `D_f,K_f` and use `(QMR2)` to obtain `(QEE1)`.

Expand the selector atoms in the Fourier basis of `D_f`:

```text
p_x=2^(-k) sum_(a in F_2^k)(-1)^(a dot x) z^a.
```

The only terms of `p_-p_x` supported in `K_f` are those with `a=0`, because
`D_f intersect K_f=<J>`. Their sum is `2^(-k)p_-`. Summing over all
`x` with `f(x)=1` proves `(QEE2)`.

If `P_f` belonged to `C[K_f]`, then `(QEE1)` would put it in `C[J]`. But on
the negative central sector it has selector eigenvalue `1` at satisfying
assignments and `0` at nonsatisfying assignments. For nonconstant `f` this
is not scalar, so `P_f` is not in `C[J]` and hence not in `C[K_f]`.

