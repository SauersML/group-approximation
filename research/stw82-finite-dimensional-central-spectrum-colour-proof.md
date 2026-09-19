---
rg: 2
id: stw82-finite-dimensional-central-spectrum-colour-proof
kind: route
title: Use Ostrand families for topology and inject active supports inside each family
target: stw82-finite-dimensional-central-spectrum-colour-bound
requires:
  - stw82-order-zero-direct-sum-support-criterion
  - stw82-zero-dimensional-central-supports-recolour-pointwise
---

Fix `epsilon>0`.  For `x in X`, let

```text
A_x={v:h_v(x)>0}.
```

Then `|A_x|<=m`.  Since `V` is finite, there is an open neighbourhood
`U_x` of `x` such that

```text
h_v(y)<epsilon                     (y in U_x, v notin A_x).  (P1)
```

The sets `U_x` form an open cover of `X`.

We use Ostrand's coloured characterization of covering dimension.  A finite
open cover of a compact metrizable space of dimension at most `n` has an
open refinement

```text
W=W_0 union ... union W_n                            (P2)
```

in which every `W_i` is a discrete family.  Compactness makes the refinement
finite.  Each `W in W` is contained in some `U_(x_W)`.  Choose a partition
of unity `(g_W)_(W in W)` subordinate to `W` with

```text
support(g_W) subset W.                               (P3)
```

The support containment in (P3) is essential.  Distinct members of one
discrete family are disjoint, so partition functions belonging to distinct
members of the same `W_i` have product zero.

For each `W`, choose an injection

```text
sigma_W:A_(x_W)->{1,...,m}.
```

For `i=0,...,n`, define

```text
c_(v,i,k)
 =sum_(W in W_i: v in A_(x_W), sigma_W(v)=k) g_W.    (P4)
```

These are positive contractions.  If `v!=w`, terms in (P4) belonging to
one `W` cannot occur for both vertices because `sigma_W` is injective;
terms belonging to different members of `W_i` have disjoint supports by
(P3).  This proves the exact orthogonality (D2).

Put `s_v=sum_(i,k)c_(v,i,k)`.  Since `sum_W g_W=1`,

```text
(1-s_v)h_v
 =sum_(W: v notin A_(x_W)) g_W h_v.                 (P5)
```

If a term occurs in (P5), then (P1), `support(g_W) subset W`, and
`W subseteq U_(x_W)` give

```text
0<=g_W h_v<epsilon g_W.
```

Summing and using `sum_W g_W=1` yields (D3), with no factor depending on
the number of refinement sets.

Every cutter lies in the common relative commutant.  Thus (D4) is cpc order
zero.  Moreover `(1-s_v)phi_v` is a positive order-zero map, so its map norm
is the norm of its value at the unit:

```text
norm(phi_v-sum_(i,k)psi_(v,i,k))
 =norm((1-s_v)h_v)<epsilon.                          (P6)
```

For fixed `(i,k)`, (D2) makes the unit supports of the maps indexed by
distinct `v` orthogonal.  The direct-sum support criterion therefore makes
their sum cpc order zero.  There are `(n+1)m` pairs `(i,k)`, proving (D6).

For (D7), apply this replacement with error `epsilon/2` to an original
nuclear approximation accurate to `epsilon/2`, duplicate its
finite-dimensional summands across the pairs `(i,k)`, and regroup by those
pairs.  The first map remains cpc, and the outgoing map remains cpc because
`0<=s_v<=1` and its unit image is dominated by that of the original
outgoing cpc map.  This gives an `((n+1)m-1)`-dimensional approximation.
