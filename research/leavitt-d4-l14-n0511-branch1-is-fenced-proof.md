---
rg: 2
id: leavitt-d4-l14-n0511-branch1-is-fenced-proof
kind: route
title: Exhaust the normal 0;511 branch-I cancellation trees
target: leavitt-d4-l14-n0511-branch1-is-fenced
requires:
  - leavitt-d4-l14-n0511-first-carrier-splits-five-ways
---

Branch I and the last carrier equation give

```text
e=p^-1, v=u^-1, x=z=1, a=du p^-1,
H=c_0d_1p^-1_2b_3.
```

The boundary has the exact reduced syllable list

```text
b^-1_3, p_2, d^-1_1, (c^-1b)_0, c_1, d_2,
(p^-1b^-1)_3, p_2, d^-1_1, (c^-1u^-1)_0,
p^-1_1, b_2, (cb^-1)_3, p_2, d^-1_1,
(c^-1du p^-1)_0, b_1, c_2, d_3.
```

The artifact enumerates all color-respecting noncrossing partitions of this
list.  There are `12,768` partitions and `180,528` choices of a distinguished
block in any of the four copies.  All other blocks are imposed as identity
equations.  Exact single-occurrence Tietze elimination reduces these to only
49 nominally nonempty target systems.  In 37, the reduced target word itself
(or its inverse) is a remaining relator.  In the other 12, the target is one
generator and the remaining relators impose two coprime powers (orders two
and three), so the target is again trivial.  Thus zero systems remain
unresolved in the universal coefficient quotient.  Distinct surviving
blocks in the target copy can be merged after the intervening identity
blocks disappear, so the distinguished-block enumeration also covers
reductions initially leaving more than one target block.  No coefficient
group specialization can produce a nontrivial one-copy boundary in branch I.
