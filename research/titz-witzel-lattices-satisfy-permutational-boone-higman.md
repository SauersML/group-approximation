---
rg: 2
id: titz-witzel-lattices-satisfy-permutational-boone-higman
kind: claim
title: The non-residually-finite Titz Mite--Witzel C2-tilde lattices satisfy permutational Boone--Higman
distinct_from:
  titz-witzel-simple-kazhdan-cat0-lattices-exist: that imports the lattices, their simple finite-index kernels and property (T); this asks whether the lattices lie in the class B_A.
  product-of-two-trees-lattices-satisfy-permutational-boone-higman: that settles the product-of-trees lattices, such as Radu's lattice, which sits inside one of these kernels up to index four; this asks for the irreducible C2-tilde lattices themselves.
artifacts:
  - research/artifacts/solve-bh-cat0-automatic-2026-09-13.md
---

**ESTABLISHED** (2026-09-18) through `titz-witzel-lattices-pbh-via-euclidean-building-lattices`,
as a special case of bh-groupoid's `euclidean-building-lattices-lie-in-permutational-bh-class`.
That is a lane proof. *(Status line updated by bh-integrate; it previously read OPEN.)*

**Verified conditionally** (bh-verify-euclid, 84896de5e,
`research/artifacts/gq-bh-verify-euclid-report.md` §7, PASS). The hypotheses match: C̃₂ is an
irreducible type of dimension 2, the buildings have thickness `q + 1`, and `Γ_i^q` acts
freely and cocompactly. The simple kernels `Γ̌_i^q` are in `B_A` too. The verification is
conditional on trust note T1. Ciobotaru–Le Bars, arXiv:2601.13092, which supplies the
topological freeness used by the Euclidean theorem, is an unrefereed preprint. Its live
barycenter chain was checked for author flags but was not re-derived.

**Update (bh-major-product, 2026-09-18): T1 is no longer needed, and a second route fires.**
- *Second route.* `titz-witzel-kernels-are-mif` is now ESTABLISHED as a literature import
  (Le Bars–Leibtag–Vigdorovich, arXiv:2609.17129, Theorem `Thm:MIF`). So
  `titz-witzel-lattices-pbh-from-mif-kernels` gives the claim through BFFHZ Theorem C, independently
  of bh-groupoid's lane proof. The authors state this consequence themselves.
- *T1 bypassed.* Apply the Euclidean theorem to the simple, type-preserving, free kernel `Γ̌`, and
  then use closure of `B_A` under finite extensions. Its only dynamical input is then topological
  freeness of `Γ̌`. That follows from their Theorem `thm:gq-open-dense-opposite-geometry`
  (`titz-witzel-nowhere-domestic-via-open-dense-opposite-geometry`), which does not use the
  Ciobotaru–Le Bars barycenter chain.

Each lattice `Γ_i^q = π_1(Y_i^q)` of Titz Mite--Witzel lies in `B_A`.
That is, it embeds in a finitely presented group with an action of type (A).

- **The kernels.** Their simple finite-index kernels `Γ̌_i^q` are finitely
  presented and simple, so the Boone--Higman conclusion holds for them
  trivially.
- **The lattices.** Each `Γ_i^q` has a nontrivial finite quotient. Main has no
  closure of the Boone--Higman class under finite-index overgroups. The class
  `B_A` does have it, by `boone-higman-type-a-class-closed-under-finite-extensions`.

**Why these lattices.** They are CAT(0) groups with property (T), and they are
not residually finite. So every tree, linear, hyperbolic and self-similar method
fails for them, as recorded on `cat0-groups-satisfy-boone-higman`.

**Route.** `titz-witzel-lattices-pbh-from-mif-kernels` reduces this claim to
`titz-witzel-kernels-are-mif`.
