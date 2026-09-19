---
rg: 2
id: atlas-large-k22-has-faithful-a5-completion-proof
kind: route
title: Verify the marked A5 completion of all four large core edges
target: atlas-large-k22-has-faithful-a5-completion
requires:
  - atlas-a4-rank-three-core
artifacts:
  - experiments/atlas_a4_large_k22_a5_certificate.g
  - experiments/atlas_a4_large_k22_low_index.g
  - research/artifacts/atlas-a4-large-k22-a5-certificate.json
---

The certificate script evaluates the ten defining relators and all subgroup
orders by exact permutation arithmetic in GAP 4.14.  The two vertex subgroups
have order six and the four edge subgroups have order twelve.  Therefore the
canonical maps from the presented `S3` and `A4` groups are injective.

The four generators are even and generate a group of order sixty, proving
that the image is `Alt(5)`.  Direct multiplication gives
`u=r^-1 b y^-1`, while `<r,y,b>` still has order sixty, proving
`(A4-K22-3)`.

Restriction of a regular representation to a subgroup repeats that
subgroup's regular representation by the index.  The indices of `S3` and
`A4` in `A5` are ten and five.  Multiplication by `336` proves the two atlas
multiplicity identities.

For the finite census, `LowIndexSubgroupsFpGroup` exhausts the thirteen
subgroups of index at most twelve returned for the local presentation.  A
coset image is retained only if both `S3` images have order six and all four
`A4` images have order twelve.  Twelve pass.  Their degree/image-order pairs
are recorded in the artifact; no conclusion about higher-index images or the
order of the universal group is drawn.
