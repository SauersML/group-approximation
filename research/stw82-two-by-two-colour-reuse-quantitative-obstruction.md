---
rg: 2
id: stw82-two-by-two-colour-reuse-quantitative-obstruction
kind: claim
title: Four support overlaps give a quantitative lower bound for every indivisible two-colour merger
distinct_from:
  stw82-indivisible-order-zero-reuse-is-graph-colouring: that gives the exact discrete chromatic criterion with no perturbation; this gives a norm lower bound which survives arbitrary small perturbations of four outgoing maps.
  stw82-complementary-cutdowns-merge-iff-near-projections: that treats one complementary pair; this permits four unrelated supports and detects both possible matchings of two endpoint colours.
---

Let

```text
alpha_i:F_i -> B,       beta_i:G_i -> B,       i=0,1,
```

be cpc order-zero maps from unital C*-algebras, and write

```text
h_i=alpha_i(1),         k_i=beta_i(1).
```

Define the two-by-two obstruction number

```text
mu = min(
  norm(h_0 h_1),
  norm(k_0 k_1),
  max(norm(h_0 k_0),norm(h_1 k_1)),
  max(norm(h_0 k_1),norm(h_1 k_0))
).                                                        (T1)
```

Suppose maps `alpha'_i,beta'_i` are assigned, without splitting, to two
global colours so that the direct sum of all maps assigned either colour is
cpc order zero.  If

```text
max_i(
  norm(alpha_i-alpha'_i),
  norm(beta_i-beta'_i)
) <= delta,                                             (T2)
```

then

```text
delta >= mu/2.                                          (T3)
```

Consequently an asymptotic indivisible two-colour compression of these four
maps is impossible whenever `mu` stays uniformly positive.  Exact
two-colour reuse (`delta=0`) forces at least one of the following: the two
`alpha` supports are orthogonal, the two `beta` supports are orthogonal, or
one of the two cross matchings consists of two orthogonal pairs.

The qualification "without splitting" is essential.  Nuclear-dimension
arguments may evade (T3) by subdividing or replacing a colour, which is
precisely what the unresolved transition-band problem may require.
