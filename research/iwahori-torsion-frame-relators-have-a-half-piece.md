---
rg: 2
id: iwahori-torsion-frame-relators-have-a-half-piece
kind: claim
title: The two torsion-frame residual words are independent and share a half piece
distinct_from:
  iwahori-two-triangle-torsion-normal-form: that makes the `C_2*C_3*C_3` frame exact and leaves two unnamed structural rows; this computes those rows as reduced free-product words and audits small cancellation and redundancy.
  bs14-two-cubic-strict-repair-constants-diverge: that gives a quantitative same-dimensional instability sequence in the old exact-core coordinates; this is a purely algebraic obstruction to simplifying the two residual words after torsion normalization.
  iwahori-uniform-infinitesimal-rigidity: that gives a uniform local differential gap at exact congruence endpoints; this shows why a classical global small-cancellation argument cannot supply basin capture away from those endpoints.
---

Let

```text
F=C_2*C_3*C_3=<x,a,b | x^2=a^3=b^3=1>.
```

Under the inverse torsion-frame substitutions

```text
t=xa,                    r=a^2 x a^2 b,               (THP1)
```

the inversion and BS covariance rows become the following cyclically
reduced free-product words:

```text
u=(xr)^2
  =x a^2 x a^2 b x a^2 x a^2 b,                     (THP2)

v=r t r^(-1)t^(-4)
  =a^2 x a^2 b x a b^2 x a^2 x a^2 x.               (THP3)
```

They have free-product syllable lengths `10` and `12`.  The cyclic
conjugate of `u` beginning at its second syllable is

```text
u'=a^2 x a^2 b x a^2 x a^2 b x.
```

It and `v` have the common initial piece

```text
p=a^2 x a^2 b x,                                     (THP4)
```

of length five, exactly half the length of `u`.  Thus the symmetrized
two-relator presentation fails `C'(1/2)`, and in particular fails every
standard `C'(1/6)` or stronger classical small-cancellation hypothesis.
The overlap is structural: `p` is the second modular involution word after
cyclic re-basing, so discarding it would discard one of the Iwahori edge
identifications.

Neither residual row follows from the other together with the torsion
relations.  The homomorphism `F->C_2` given by

```text
x |-> nontrivial,             a,b |->1
```

sends `u` to `1` but `v` to the nontrivial involution.  Conversely the map
`F->C_3` given by

```text
x |->1,              a,b |->g
```

for a generator `g` sends `v` to `1` but `u` to `g`.  Hence no Tietze
deletion of either structural row is possible from the exact torsion frame.

This rules out two cheap qualitative closures of the regular basin:
classical free-product small cancellation and redundancy of one structural
row.  It does not refute a flexible rank-dilation theorem or a genuinely
analytic two-row inequality; those remain the viable targets.

