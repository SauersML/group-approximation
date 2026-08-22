---
rg: 2
id: leavitt-d4-rank8-orientations-are-fenced-proof
kind: route
title: Fence the simple projection class and the exotic malnormality class
target: leavitt-d4-rank8-orientations-are-fenced
requires:
  - leavitt-d4-latin-triangle-reduction
---

The attached exact rank enumerator gives

```text
rank 7: 2,       rank 8: 5,       rank 9: 3,       rank 10: 206.
```

Four rank-eight orientations are the cyclic/inverse class represented by
`(N,N,I)`.  Their carrier matches give the same four-unit Latin family as in
the displayed orientation.  For the representative, its boundary projections
are

```text
K0=b^-1 a b^-1 d c^-1 b,   K1=c^-1 b c^-1 a d^-1 c,
K2=d^-1 c d^-1 b a^-1 d,   K3=a^-1 d a^-1 c b^-1 a.
```

Assume `K1=K2=K3=1`.  The first equation gives `d=b c^-1a`.  Put
`x=c^-1a`, so `d=bx`; the second becomes

```text
x^-1 (b^-1 c x^-2 c^-1 b) x=1,
```

and hence `x^2=1`.  But then
`K0=b^-1(c x)c^-1(c x)c^-1b=1`.  Cyclic relabeling and inversion cover all
four orientations.

The exotic fifth orientation has face triples

```text
(A^-1,P^-1,Q^-1),       (B,R,Q^-1),       (P,C^-1,R).
```

Its carrier matches are `C1=C0`, `C2=B1`, and
`A2=H^-1B0^-1H`.  The first two force

```text
g0=1, g1=g9^-1, g6=g7=g8=1, g5=g2.
```

Then `H=g2_1 g3_0 g4_1 g2_2`, `B0=g9_3`, and `A2=g3_3`.  Free-factor
malnormality applied to the last carrier match leaves only
`g3=g9=1`: the alternative would put `H` in copy 3, but `H` has no copy-3
syllable, and `H=1` would also force `g3=1`.

Put `k=g2`, `m=g4`, `p=km`.  The eliminated boundary is exactly

```text
k^-1_1 m^-1_0 p_1 k_2 (p k^-1)_3 p^-1_2.                (1)
```

If `k,m,p,pk^-1` are nontrivial, `(1)` is reduced of length six.  If `k=1`
or `p=1`, it remains reduced of length four; if `m=1`, it is the identity.
Thus it is never a nontrivial one-copy word.  This exhausts rank eight.
