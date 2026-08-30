---
rg: 2
id: stw63-relative-corner-equivalence-proof
kind: route
title: Read an implementing unitary as the lower-left corner
target: stw63-aue-is-relative-corner-equivalence
requires: []
---

Suppose first that unitaries `u_n in B` implement approximate unitary
equivalence.  Their class `u in B_infinity` satisfies

```text
u phi(a) = psi(a)u       (a in A).
```

The matrix `x=e_21 tensor u` therefore belongs to `D` and satisfies
`x^*x=p`, `xx^*=q`.

Conversely, let `x in D` have `x^*x=p` and `xx^*=q`.  These equations force
`x=qxp`, so its only possible nonzero matrix entry is the lower-left entry
`u in B_infinity`.  The same equations say that `u` is unitary, while
`x pi(a)=pi(a)x` says

```text
u phi(a)=psi(a)u.                                      (2)
```

There is no hidden unitary-lifting assumption here.  Choose an arbitrary
bounded representative `(b_n)` of `u`.  The unitary equations in the
quotient give

```text
||b_n^*b_n-1|| -> 0,       ||b_nb_n^*-1|| -> 0.
```

For all sufficiently large `n`, `b_n` is invertible.  Its polar unitary
`u_n=b_n(b_n^*b_n)^(-1/2)` belongs to `B` and satisfies `||u_n-b_n||->0`.
Lifting (2) along this sequence gives
`||u_n phi(a)u_n^*-psi(a)||->0` for every `a in A`.

In the forward direction, separability turns the usual finite-set definition
of approximate unitary equivalence into one sequence by diagonalization.  In
the reverse direction, (2) already gives pointwise convergence along the
lifted sequence.
