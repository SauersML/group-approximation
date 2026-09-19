---
rg: 2
id: group-algebra-mark-reverse-kleene-collapse-proof
kind: route
title: Enumerate zero proofs for the algebra mark and compare its canonical norm with microstate collapse
target: group-algebra-mark-reverse-kleene-collapse
requires: []
---

Equality to zero of a finite rational group-algebra expression is recursively
enumerable.  After clearing denominators, write

```text
p=sum_(j=1)^m n_j w_j.
```

In `Z[Gamma]`, this is zero exactly when the finitely many words can be
partitioned into blocks of equal group elements and the coefficient sum in
every block is zero.  Enumerate consequences of the finite group
presentation.  If `p=0`, eventually the enumeration proves enough pairwise
word equalities to certify its actual equality blocks; conversely every
certificate found this way is sound.  Thus a Turing machine can halt exactly
when `p=0`.

Apply Kleene's recursion theorem to the machine which, knowing its own index
`e`, computes `(Gamma_e,p_e)` and searches for such a zero certificate.  Let
`e_*` be its fixed point.  It cannot halt: halting would certify `p_(e_*)=0`,
whereas `(GAK2)` would give `p_(e_*)!=0`.  Moreover `p_(e_*)` cannot be zero,
because zero equality is recursively enumerable and would make the machine
halt.  Hence

```text
e_* does not halt,             p_(e_*) != 0.           (1)
```

Suppose `Gamma_(e_*)` were hyperlinear.  Apply canonical-trace microstates to
a growing finite word set containing the support of `p_(e_*)`, the fixed
relators, and the finitely many moment side tests.  Their relator defects tend
to zero and their moments tend to the canonical group trace, so `(GAK3)` gives

```text
||p_(e_*)(U_n)||_2 -> 0.                              (2)
```

On the other hand, multiplication and trace convergence on the finite support
of `p^*p` give

```text
||p_(e_*)(U_n)||_2^2
 -> tau_(Gamma_(e_*))(p_(e_*)^*p_(e_*))
 = ||p_(e_*)||_(2,tau)^2 > 0.                         (3)
```

The last inequality follows from faithfulness of the canonical trace on the
group algebra: after collecting equal group elements it is the sum of the
squared absolute coefficients.  Equations `(2)` and `(3)` contradict each
other, proving nonhyperlinearity.

