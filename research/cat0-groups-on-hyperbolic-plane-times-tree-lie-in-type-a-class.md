---
rg: 2
id: cat0-groups-on-hyperbolic-plane-times-tree-lie-in-type-a-class
kind: claim
title: Every group acting geometrically on the hyperbolic plane times a locally finite tree lies in the permutational Boone--Higman class, and so does every group on a symmetric space times a tree whose fibre groups are residually finite irreducible arithmetic lattices
distinct_from:
  cat0-groups-with-a-tree-factor-lie-in-type-a-class: that reduces Y x T to a faithful member of BS_G for the fibre group G and settles Y = E^n; this settles Y = H^2 and symmetric spaces with arithmetic residually finite fibres.
  arithmetic-lie-lattices-have-faithful-bs-members: that is the statement about BS_G; this applies it to CAT(0) groups with a tree factor.
  cat0-groups-satisfy-boone-higman: that is survey item (10) for all CAT(0) groups; this is a subclass containing many non-linear, possibly non-residually-finite groups.
---

**ESTABLISHED** through `cat0-hyperbolic-plane-tree-type-a-proof` (lane proof; referee a PASS,
`research/artifacts/gq-referee-a-arithmetic-lie-lattices-and-hyperbolic-plane-tree.md`; referee b PASS,
`research/artifacts/gq-referee-b-arithmetic-lie-lattices-and-hyperbolic-plane-tree.md`;
no priority claimed).

1. Let `Γ` act properly and cocompactly by isometries on `H^2 × T`, with `T` a
   locally finite tree. Then `Γ ∈ B_A`. So every subgroup of `Γ` embeds in a
   finitely presented simple group.
2. Let `X` be a symmetric space of noncompact type, and let `Γ` act properly and
   cocompactly on `X × T` preserving the product decomposition. Suppose that for
   some vertex `v` of `T` the stabilizer `Γ_v` is residually finite and its image
   in `Isom(X)` is an irreducible arithmetic lattice, for example any irreducible
   lattice when `X` has real rank `>= 2`, by Margulis. Then `Γ ∈ B_A`. Reducible
   fibre lattices are not covered here.

**Remarks.**
- `Γ` itself need not be linear or residually finite. Only the fibre groups are
  constrained.
- For `X` irreducible of real rank `>= 2`, the arithmetic hypothesis is automatic,
  and only residual finiteness of `Γ_v` remains. It holds, for example, when `Γ_v`
  acts faithfully on `X`.
