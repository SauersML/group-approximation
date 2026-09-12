---
rg: 2
id: atlas-q96-c144-cycle-has-faithful-a8-quotient
kind: claim
title: The noncentral Q96-C144 cycle has four faithful-vertex A8 quotients
artifacts:
  - experiments/atlas_a4_q96_c144_a8_quotients.g
  - research/artifacts/atlas-a4-q96-c144-a8-quotients.json
distinct_from:
  atlas-q96-to-c144-cycle-is-six-generator-finite-vertex-test: that isolates the exact binary test and records inconclusive generic coset enumeration; this solves it by a target-specific exhaustive A8 quotient calculation.
  atlas-a8-carrier-reaches-third-large-core-edge: that gives one explicit degree-eight carrier through three large core edges; this classifies the A8 epimorphisms of the noncentral Q96 finite-vertex cycle and certifies every vertex order.
  atlas-affine-q96-has-no-s3-square-extension: that excludes one affine embedding of Q96 in AGL5(2); this changes the marked Q96 embedding and gives positive completions already in A8.
---

Let `Gamma_96,144` be the six-generator cycle in
`atlas-q96-to-c144-cycle-is-six-generator-finite-vertex-test`.  Exact GAP
quotient enumeration gives

```text
#Epi(Gamma_96,144,A8)/Aut(A8)=24.                         (A8-QC-1)
```

For each epimorphism, record the four marked subgroup orders in the order

```text
F'=<r,z,c,u>,   Q=<c,u,t>,   J=<t,s,c>,   C=<r,z,st>.
```

The complete histogram is

```text
[36,48,24, 36] : 8,       [36,48,24,144] : 8,
[36,96,24, 36] : 4,       [36,96,24,144] : 4.           (A8-QC-2)
```

Hence exactly four quotient classes preserve all four finite vertices.  One
certificate, with permutations written as one-based image lists in generator
order `r,z,c,u,t,s`, is

```text
[2,4,7,1,5,3,6,8],       [2,4,6,1,5,7,3,8],
[6,3,2,7,8,1,4,5],       [3,6,1,7,8,2,4,5],
[1,2,5,7,8,4,6,3],       [2,1,4,3,6,5,8,7].            (A8-QC-3)
```

These permutations generate all of `A8`, of order `20160`, and the four
marked subgroups have orders `[36,96,24,144]`.  The first noncentral
forward/core cycle therefore has an exact regular-margin finite carrier; the
next obstruction must use another packet edge beyond this six-generator
support.

The same exhaustive list also evaluates the four large-rectangle edge words
in their canonical order.  Two faithful classes have order profile
`[3,3,3,7]` and two have `[3,3,7,7]`.  Thus two classes absorb the next
(third) large-core edge, but none absorbs the fourth inside `A8`.  The fourth
edge is again the first carrier-specific seam; its failure here is not a
universal obstruction.
