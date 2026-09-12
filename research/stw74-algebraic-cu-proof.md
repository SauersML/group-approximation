---
rg: 2
id: stw74-algebraic-cu-proof
kind: route
title: Extract a compact class from an algebraic approximation and realize it by a projection
target: stw74-algebraic-cu-characterizes-pure-infiniteness
requires:
  - stw74-all-stabilized-projections-are-properly-infinite
  - stw74-counterexamples-are-unstably-projectionless
  - stw74-every-nonzero-cu-class-is-a-finite-unit-root
---

Put `u=[1_A]`.  First suppose that `Cu(A)` is algebraic, and let
`0!=x in Cu(A)`.  Write

```text
x = sup_k c_k,             c_k compact,             c_k<=c_(k+1).
```

Some `c_k` is nonzero; fix such a `c`.  We use the standard compact-class
realization fact for simple C-star algebras: every nonzero compact element of
`Cu(A)` is represented by a projection in `A tensor K`.  Thus `c=[p]` for a
nonzero projection `p`.

The stabilized-projection theorem makes `p` properly infinite.  It is full in the simple
algebra `A tensor K`, so compactness of `u` gives

```text
u <= N[p]
```

for some finite `N`.  Proper infiniteness gives `N[p]=[p]`.  Conversely
`[p]<=u`: the unit is the largest Cuntz class, since any finite matrix unit is
absorbed by the properly infinite unit and every positive element of
`A tensor K` is the supremum of its finite-matrix cutdowns.  Hence `[p]=u`.
Since `[p]=c<=x<=u`, it follows that `x=u`.

Therefore every nonzero positive element `a` satisfies `u<=[a]`.  A
projection Cuntz below a positive element is Murray--von Neumann equivalent
to a projection in its hereditary subalgebra, so every nonzero hereditary
subalgebra contains a projection equivalent to `1_A`.  Equivalently, `A` is
purely infinite.

Conversely, if `A` is purely infinite and simple, any two nonzero positive
elements are Cuntz equivalent.  Hence

```text
Cu(A) = {0,u}.
```

The projection class `u` is compact, so this two-element Cu-semigroup is
algebraic.

Finally, suppose `A` is a counterexample and choose a nonzero positive
element `a` in its projectionless hereditary corner.  If a nonzero compact
`c<=[a]` existed, compact-class realization would give a nonzero projection
Cuntz below `a`, and hence a nonzero projection in `Her_A(a)`, a
contradiction.  The finite-unit-root theorem supplies `n[a]=u` for some
finite `n`.  Thus `x=[a]` is the asserted compact-free finite root, and
`Cu(A)` cannot be algebraic.

The only external background fact used above is compact-class realization
for simple C-star algebras.  It is recalled explicitly in the preliminaries
of Andrew Toms, *Homotopies of constant Cuntz class*, arXiv:2202.10428, with
the original references given there.  All LXXIV-specific deductions are
internal.
