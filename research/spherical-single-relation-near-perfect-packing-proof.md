---
rg: 2
id: spherical-single-relation-near-perfect-packing-proof
kind: route
title: A Pippenger--Spencer matching in the tighter product triangle hypergraph
target: spherical-single-relation-near-perfect-packing
requires: []
---

Use a tighter radius `r_0=1/2`.  On three abstract copies `I,J,L` of the
cloud index set, form a 3-partite 3-uniform hypergraph with edge `(i,j,l)` iff

```text
||U_h x_i-x_j|| <= r_0,
||U_g x_j-x_l|| <= r_0,
||U_g U_h x_i-x_l|| <= r_0.
```

The third condition deliberately uses the exact matrix product rather than
`U_k`; the microstate defect will be spent only after the matching is found.
Put

```text
a_i=U_h x_i,   b_j=x_j,   c_l=U_g^*x_l.
```

Then the three edge conditions are simply

```text
||a_i-b_j||, ||b_j-c_l||, ||a_i-c_l|| <= r_0.
```

For distinct numerical indices `i,j,l`, these are three independent uniform
sphere points after fixing any one of them.  Let `alpha_d>0` be the probability
that two independent uniform points together with one fixed unit vector form
such a triangle.  Positivity is elementary: it is enough that both random
points lie in the radius-`r_0/2` cap around the fixed vector.

For a fixed vertex, the `N^2+O(N)` off-diagonal candidate pairs therefore have
expected degree

```text
D=(1+o(1)) N^2 alpha_d,
```

independently of the part and of the fixed vertex.  Uniform concentration does
not require independence of all edge indicators.  Conditional on the fixed
vertex, changing one other cloud point affects at most `2N+O(1)` incident
triples.  McDiarmid's bounded-differences inequality thus gives tails

```text
Pr[|deg-D| > eps D]
 <= 2 exp(-Omega(eps^2 N alpha_d^2)).
```

Choose `N=N(d)` so large that, for some `eps_d->0`,

```text
eps_d^2 N alpha_d^2 >> log N,
N alpha_d -> infinity.
```

A union bound over the `3N` vertices then makes the hypergraph
`(1+o(1))D`-regular.  Its maximum pair-codegree is deterministically at most
`N`: two vertices in different parts leave only the third index free, while
two vertices in one part lie in no common edge.  Hence

```text
Delta_2/D <= (1+o(1))/(N alpha_d) -> 0.
```

Pippenger--Spencer, *Asymptotic behavior of the chromatic index for
hypergraphs*, J. Combin. Theory Ser. A 51 (1989), 24--42,
DOI `10.1016/0097-3165(89)90074-5`, proves that a fixed-uniformity almost
regular hypergraph with negligible maximum codegree has an almost-perfect
matching.  Apply it here to obtain a matching of `(1-o(1))N` triples.

Now spend the group-law defect.  Put

```text
eta_i=||(U_gU_h-U_k)x_i||.
```

Its spherical mean square is exactly `||U_gU_h-U_k||_2^2`, so Markov and the
law of large numbers show that all but `o(N)` roots have `eta_i<=1/2` when the
normalized-HS defect tends to zero.  Delete the matching triples whose
`I`-vertex is bad.  On every surviving triple `(i,j,l)`, define

```text
sigma_h(i)=j,   sigma_g(j)=l,   sigma_k(i)=l.
```

Because the triples form a matching, these are partial bijections with
`1-o(1)` domains and ranges.  The `h` and `g` edges have radius at most `1/2`,
and

```text
||U_k x_i-x_l||
 <= eta_i + ||U_gU_h x_i-x_l||
 <= 1,
```

so the `k` edge is a radius-one candidate as well.  Finally the displayed
definitions give `sigma_g sigma_h = sigma_k` exactly on every surviving root.
