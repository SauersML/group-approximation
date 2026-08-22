---
rg: 2
id: atlas-augmented-relations-have-unbounded-chart-width
kind: claim
title: The augmented Atlas relations have an infinite chart-coset graph and cannot imply bounded alternating width
distinct_from:
  atlas-charts-overlap-trivially: that computes the chart intersection and the free kernel for the full canonical atlas target; this applies it to the packet plus 19243 plus q14 universal completion and rules out the proposed global-width shortcut.
  atlas-q14-finite-quotient-is-simple-overgroup-test: that reduces finite escapes to finite simple marked pairs; this proves that bounded width cannot come from the marked relations or simplicity alone without a genuinely finite theorem.
  atlas-q14-simple-overgroup-index-is-at-least-32: that obtains a lower index sieve from finite permutation theory; this explains why the sieve cannot be converted into an upper bound by a presentation-level diameter argument.
---

Let

```text
Gamma_+=(A8*A8)/<<packet,q_19243,q_14>>,
A,B < Gamma_+                                       (UAW1)
```

be its two chart copies.  Then `Gamma_+` is infinite, `A intersect B=1`, and
for every finite `k`,

```text
Gamma_+ != (AB)^k.                                  (UAW2)
```

More geometrically, let `Q` be the canonical binary-Leavitt chart image and
form the bipartite incidence graph

```text
V(X)=Q/A disjointUnion Q/B,
E(X)=Q,                                               (UAW3)
```

where the edge indexed by `g` joins `gA` to `gB`.  Then `X` is connected,
infinite, locally finite, and biregular of degree `20160` on both sides.
Consequently

```text
diam(X)=infinity.                                    (UAW4)
```

The twelve cross-`A4` packet edges, q14, and `q_19243` merely provide closed
walks of lengths 6, 4, and 8 in this graph.  They do not bound its diameter.
Thus no manipulation of those exact relations can prove a universal identity
such as

```text
Gamma_+=ABAB
```

or any bounded alternating-product analogue.

There is nevertheless a precise conditional payoff in a finite quotient.
For a finite quotient `S=<A,B>`, put `T=A intersect B`,

```text
n=[S:A],       d=[A:T]=[B:T].                        (UAW5)
```

Its incidence graph has `2n` vertices and degree `d`.  If a genuinely
finite-simple theorem bounded its diameter by `D`, the Moore ball count would
give

```text
2n <= 1+d sum_(j=0)^(D-1) (d-1)^j.                  (UAW6)
```

In particular, on the first index-sieve intersection types one has
`d in {8,15,28}`, so a uniform `D` would indeed bound `|S|=20160n` and leave
only finitely many simple groups.

The point is that `(UAW6)` cannot be reached from the presentation alone.
Any such diameter theorem must use finiteness of `S` in an essential way—more
than the local cross-`A4` amalgams, q14 centralizer, q19243 collision, or
abstract simplicity.  The infinite Leavitt image is an exact countermodel to
every relation-only bounded-width assertion.
