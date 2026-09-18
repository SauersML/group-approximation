---
rg: 2
id: rel-hyperbolic-bh-permanence-implies-free-product-closure
kind: claim
title: Boone--Higman permanence under relative hyperbolicity implies closure of the Boone--Higman class under free products
distinct_from:
  bh-class-free-products-iff-joint-embedding-and-free-z: that shows free-product closure is equivalent to joint embedding plus the U * Z condition; this shows relative-hyperbolic permanence implies free-product closure, so it is at least as hard.
  rel-hyperbolic-groups-with-bh-peripherals-satisfy-bh: that is the permanence statement itself (OPEN); this is one consequence of it.
---

**ESTABLISHED** by the argument below. Lane proof, elementary, not reviewed. No
priority claimed.

Let `𝓑` be the class of finitely generated groups that embed in a finitely
presented simple group.

**Claim.** If `rel-hyperbolic-groups-with-bh-peripherals-satisfy-bh` holds, then
`𝓑` is closed under free products of two groups. By
`bh-class-free-products-iff-joint-embedding-and-free-z`, the permanence statement
therefore implies joint embedding (JE) for finitely presented simple groups and
`U * Z ∈ 𝓑` for every finitely presented simple `U` (FZ). Both are open, so
relative-hyperbolic permanence is at least as hard as free-product closure.

**Proof.** Let `A, B ∈ 𝓑`.
- `A * B` is finitely generated. It is hyperbolic relative to `{A, B}`: it acts on
  its Bass--Serre tree with one orbit of edges and trivial edge stabilizers, and
  a tree is a fine hyperbolic graph, so this is Bowditch's definition, with the
  infinite vertex stabilizers (the conjugates of `A` and `B`) as the maximal
  parabolic subgroups. (If `A` or `B` is finite it is simply not listed; the
  conclusion is unchanged.) In Osin's language, the relative presentation with no
  extra generators and no relators has relative area zero.
- `A` and `B` have solvable word problem (`simple-envelope-forces-solvable-word-problem`),
  so `A * B` does, by reduced forms.
- The peripheral subgroups `A`, `B` lie in `𝓑`.
So the permanence statement applies and gives `A * B ∈ 𝓑`.
