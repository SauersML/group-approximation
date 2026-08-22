---
rg: 2
id: atlas-a8-carrier-reaches-third-large-core-edge-proof
kind: route
title: Verify the degree-eight three-edge carrier and low-index mask census
target: atlas-a8-carrier-reaches-third-large-core-edge
requires:
  - atlas-forward-collision-bass-serre-reduction
artifacts:
  - experiments/atlas_a4_three_large_core_a8_certificate.g
  - experiments/atlas_a4_low_index_next_core_screen.g
  - research/artifacts/atlas-a4-three-large-core-a8-certificate.json
---

The first artifact hard-codes the six one-based permutation lists.  GAP 4.14
checks all minimal relators, collision, the four local support orders, the
three A4 subgroup orders, and the four-bit mask `(A4-A8-3EDGE)` by exact
permutation multiplication.  The generated group has order `20160` and lies
in `Alt(8)`, proving equality with `A8` without a database identification.
The fourth product has exact order seven.  Since cubing is injective on its
cyclic subgroup, adjoining its cube as a relator kills a nonidentity element;
the simplicity of `A8` then kills the whole carrier image.

For the census, `LowIndexSubgroupsFpGroup` exhausts index at most twelve for
the five-generator minimal presentation.  A coset action is retained exactly
when the images of `C,F,K` have orders `144,18,6`.  For each retained image,
the script enumerates the transporter in the symmetric group which centralizes
`<z,c>`, takes `r` to `r^-1`, is involutive, and satisfies `(u t^-1)^3=1`.
It retains only `u` with `|<r,z,c,u>|=36`, then evaluates all four large-core
relations.  This yields the stated counts and masks.  No inference beyond
index twelve is made.
