---
rg: 2
id: finite-s6-selector-centralizer-proof
kind: route
title: Use the complement S4 centralizer and the three-cycle character class
target: finite-s6-selector-centralizer-pins-common-pivot-arm
requires: []
---

An element centralizing `K=Sym(Delta)` preserves its unique four-point orbit
`Delta` and its two fixed points `{i,p}`.  Its restriction to `Delta` lies in
the center of `S_4`, which is trivial, while its restriction to `{i,p}` is
arbitrary.  This proves `(FSC2)`.

If `x in Delta`, choose an incident edge `z` of the path
`j--k--l--q`.  The transpositions `s_x=(x p)` and `z` share exactly the
letter `x`, so their commutator is a three-cycle.  The transpositions
`s_i=(i p)` and `s_x` share exactly `p`, so `s_i^(-1)s_x` is also a
three-cycle.  These elements are conjugate.  For the normalized character
of any `pi`,

```text
||pi(s_x)-pi(s_i)||_2^2
 =2-2 Re tr(pi(s_i^(-1)s_x))
 =2-2 Re tr(pi([s_x,z]))
 =||[pi(s_x),pi(z)]-I||_2^2.
```

This proves `(FSC3)`.  Finally telescope

```text
c_x-c_i=(s_x-s_i)t_x+s_i(t_x-t_i)
```

and use `t_x=s_x^r`, unitary invariance, and `(FSC3)` to obtain `(FSC4)`.

