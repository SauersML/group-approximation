---
rg: 2
id: relative-c-sixth-incidence-closes-placement
kind: route
title: Apply relative Greendlinger, separate Pauli clouds, and Higman-embed the address group
target: colored-cayley-pauli-incidence-separation
requires:
  - relative-c-sixth-pauli-incidence-labeling
  - relative-c-sixth-protects-sign-double-cosets
  - sign-double-cosets-separate-pauli-clouds
artifacts:
  - research/artifacts/relative-small-cancellation-occurrence-support-2026-08-21.md
---

Form the recursive relative graphical-small-cancellation quotient `G` of
`(RPC1)`.  The graphical `Gr'(1/6)` embedding theorem gives actual addresses
for the occurrence vertices and keeps every local edge in the prescribed
finite offset set.  By
`relative-c-sixth-protects-sign-double-cosets`,

```text
H_X P_0 H_Z  intersect  H_X P_1 H_Z = empty.                  (1)
```

The Pauli sign table separates rows and columns, so
`sign-double-cosets-separate-pauli-clouds` turns `(1)` into distinct X and Z
cloud cosets.

The group `G` is finitely generated and recursively presented.  Apply
Higman's embedding theorem to embed it in a finitely presented group `A`.
The images of the finitely many offsets are fixed finite words in `A`.
Injectivity preserves `(1)` and the cloud-coset inequalities: every factor
in a proposed equality still lies in the embedded copy of `G`.  Therefore
all four clauses of `colored-cayley-pauli-incidence-separation` hold in `A`.

For a primary-source strengthening, Wagner arXiv:2404.00841v2, Theorem A
provides a quasi-isometric malnormal CEP Higman embedding.  By
`higman-embedding-preserves-occurrence-coset-separation`, ordinary injectivity
already proves the coset assertions above, while CEP also preserves any source
normal-closure firewall.

No quasi-isometric or quantitative Higman theorem is needed.  Every tested
occurrence relation is a conjugate of a relator involving one of the fixed
offset words, so its normalized-HS cost is independent of the length of the
address.
