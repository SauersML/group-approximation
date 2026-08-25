---
rg: 2
id: one-mark-gram-collapse-reverse-kleene-proof
kind: route
title: Compare one collapsing subsequence with the finite canonical Gram matrix
target: one-mark-gram-collapse-suffices-for-reverse-kleene
requires:
  - canonical-profile-kleene-higman
  - exact-group-algebra-death-cannot-code-nonhalting
---

As in `canonical-profile-kleene-higman`, uniformly enumerate proofs that
`p_e=0` and apply Kleene's recursion theorem to the machine which searches
for such a proof about its own compiled mark.  At the fixed point `e_*`,
halting would contradict `(MGC2)`, while completeness of proof enumeration
shows

```text
e_* nonhalts,            p_(e_*)!=0 in Q[Gamma_(e_*)]. (1)
```

Suppose `Gamma_(e_*)` were hyperlinear.  By `(MGC4)` there is one mark-Gram
canonical microstate sequence `U_n` with

```text
liminf_n ||p_(e_*)(U_n)||_2=0.                          (2)
```

On the other hand, `(MGC3)` gives

```text
||p_(e_*)(U_n)||_2^2
 = sum_(i,j) conjugate(c_i)c_j
     tr(w_i(U_n)^*w_j(U_n))
 -> tau_(Gamma_(e_*))(p_(e_*)^*p_(e_*)).               (3)
```

After grouping support words which represent the same group element, the
right side of `(3)` is

```text
sum_C |sum_(i in C)c_i|^2,
```

where `C` runs over equality classes.  It is strictly positive by `(1)`.
Thus the norm sequence in `(3)` converges to a positive number, contradicting
the zero liminf in `(2)`.  Hence `Gamma_(e_*)` is nonhyperlinear.

The fixed-point group is finitely generated and recursively presented.
Effective Higman embedding puts it inside an effectively specified finitely
presented group, and hyperlinearity passes to subgroups.  Therefore the host
is finitely presented and nonhyperlinear.

Only the `m^2` moments displayed in `(MGC3)` enter `(3)`.  Full canonical
moment convergence is one sufficient source of them, not an additional
hypothesis needed by the diagonal itself.
