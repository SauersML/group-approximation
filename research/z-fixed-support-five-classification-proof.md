---
rg: 2
id: z-fixed-support-five-classification-proof
kind: route
title: Classify the even-degree four-edge C3 coset incidence graph
target: z-fixed-support-five-hecke-normal-form
requires: []
artifacts:
  - research/artifacts/leavitt-corner-small-rank-coset-classification-2026-08-21.md
---

## Direct proof

The left/right parity rule from `z-fixed-support-three-no-go-proof` shows that
the support meets `H` in one or three points; five is impossible because
`|H|=3`.

With three points in `H`, the two remaining points lie in one right and one
left coset; their cell has size at
least two, so `H intersect xHx^(-1)` is nontrivial and its representative
normalizes the order-three group `H`.  The support lies in `N_G(H)`.

With one point in `H`, the other four split into two pairs of right cosets and
two pairs of left cosets.  Their bipartite incidence graph is two-regular, so
it is either two doubled edges or a four-cycle.  A doubled cell has at least
two elements, again forcing its representative into `N_G(H)`; two doubled
edges give case 1.

For a four-cycle choose its upper-left element `x`.  Write the adjacent
elements as `rx` and `xs` with nonidentity `r,s in H`.  If `x` normalized
`H`, all four vertices lie in the normalizer and this is case 1.  Otherwise
the intersection of a left and right `H`-coset has at most one element, so the
opposite corner is forced to be `rxs`.  The four-cycle sum is exactly

```text
[x]+[rx]+[xs]+[rxs]=(1+[r])[x](1+[s]),
```

which is case 2.
