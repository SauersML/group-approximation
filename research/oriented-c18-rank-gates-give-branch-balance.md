---
rg: 2
id: oriented-c18-rank-gates-give-branch-balance
kind: claim
title: Two oriented C18 rank gates give exact active-plus-exit branch balance
artifacts:
  - experiments/fanizza_oriented_c18_exit_compiler.py
distinct_from:
  fanizza-final-bcs-has-fixed-nonlinear-menu: that records C18's 20 forbidden assignments as one Boolean constraint; this replaces them, only on the forward source carrier, by 20 oriented exit occurrences counted with multiplicity.
  binary-cut-projection-recurrence-gives-bfe1: that converts a supplied projection recurrence residual into a scalar balance; this proves the required balance pointwise on the C18 spectral atoms after packet replacement.
  fanizza-bad-atoms-have-symmetric-frames: that builds one frame for each original forbidden atom; this recompiles the recurrence into two oriented predicates and obtains a common hard root without a coordinate swap.
---

Write the first three C18 projection bits as `(p,q,r)` and let `h` be the
indicator that the last three sign bits have even parity.  Define two Boolean
exit predicates

```text
e_1 = h [p+q-r>0],
e_2 = h [(p,q,r)=110].                                 (OCB1)
```

On the phase-even carrier, the following **integer**, not mod-two,
inequalities hold pointwise:

```text
p+q <= r+e_1+e_2,
e_1+e_2 <= p+q.                                        (OCB2)
```

The first gives the two-child balance `(BFE1)` after interpreting `e_1,e_2`
as exit masses.  The second gives the one-exit-per-source bound `(BFE2)` in
the correct total-source normalization.  At the double-source atom `110`,
both exits fire; at `111` only one fires.  The only original C18 bad atom not
seen by `e_1` is `001`, which has `p+q=0` and therefore zero intersection with
the forward source carrier.  More precisely, if

```text
f_C18=h[p+q!=r],       s=[p+q>0],
```

then

```text
f_C18 s=e_1.                                           (OCB3)
```

Thus the corner-localized C18 forbidden mass on the source carrier is exactly
the first oriented exit mass, while `e_2` supplies the second unit required
by the size-two residual at `110`.

The oriented truth tables have `16` and `4` atoms.  Their optimized OBDD
Schur compilers have baseline ranks `10` and `9`, hence matrix sizes `11` and
`10`, both smaller than the size-12 compiler for undirected C18.  Every one
of the 20 oriented occurrences admits a weight-at-most-two source-fixed frame
with

```text
K_sym=span{e_01,e_23,e_03+e_12},
hard form=e_02^*,
reverse coefficient sign J=+1.                         (OCB4)
```

So the two exits enter the same E5 top root directly.  The total number of
rank-one exit occurrences remains 20: removing the four source-free `001`
atoms and counting the four `110` atoms twice preserves the finite budget.

This is an oriented recurrence compiler, not an equivalent replacement of
C18 on arbitrary corners.  Its use is valid precisely after cutting to the
forward source carrier, where `(OCB3)` retains the full C18 soundness mass.
