---
rg: 2
id: rank-five-rectangle-is-one-letter-hecke-element
kind: claim
title: The rank-five rectangle is corner-unit equivalent to one Hecke letter plus the corner identity
distinct_from:
  z-fixed-support-five-hecke-normal-form: that classifies the five group-basis terms as a double-coset rectangle; this removes its two C3 edge labels by units in the nontrivial Fourier corner and leaves one group letter.
  constant-c3-normalizer-is-f4-leavitt-semilinear: that identifies the other, normalizer-supported rank-five branch; this normalizes the rectangle branch with its letter explicitly outside the normalizer.
  finite-subgroup-hecke-literals-cannot-block-escape: that classifies when a single compression `qgq` is itself a projection; this concerns one-sided invertibility of the sum of the corner identity and one compressed letter.
artifacts:
  - research/artifacts/rank-five-rectangle-one-letter-reduction-2026-08-21.md
---

Let `H=<g>=C_3`, `z=sum_H[h]`, and `e=1+z=[g]+[g^2]`.  Suppose the five-term
unitized factor is in the rectangle branch

```text
alpha=[h_0]+(1+[r])[x](1+[s]),
h_0 in H,       r,s in H minus {1},       x notin N_G(H).
```

Its corner component `a=e alpha e=alpha+z` is, up to multiplication on the
left and right by units of `eF_2[H]e`, equal to

```text
e(1+[y])e
```

for one `y notin N_G(H)`.  Hence a one-sided inverse for the rectangle factor
is equivalent to a one-sided inverse for this one-letter Hecke element in
`eF_2[G]e`, with the reverse defect preserved up to corner-unit conjugation.

Together with `constant-c3-normalizer-is-f4-leavitt-semilinear`, this is an
exhaustive two-branch reduction of the support-five side of the surviving
`(5,7)` profile: an `F_4`-Leavitt semilinear branch or a one-letter Hecke
branch.
