---
rg: 2
id: hyperbolic-kac-moody-lattices-are-torsion-locally-finite
kind: claim
title: Kac–Moody lattices over finite fields whose Weyl group contains no Z^2 are torsion locally finite, so the finitely presented simple Kazhdan Kac–Moody groups with hyperbolic Weyl group contain no infinite finitely generated periodic group
distinct_from:
  two-dim-cat0-product-groups-are-torsion-locally-finite: that treats Kac–Moody lattices whose buildings are 2-dimensional (no spherical triple in W), through Norin–Osajda–Przytycki; this treats those whose Weyl group has no Z^2 (word-hyperbolic W), in any dimension, through Haettel–Osajda and Caprace–Haglund. The two classes overlap (e.g. the (2,4,6) triangle group) and neither contains the other.
  fp-simple-kac-moody-lattices-satisfy-pbh: that puts the finitely presented simple Kac–Moody groups in the permutational Boone–Higman class; this restricts their periodic subgroups when W is hyperbolic.
  simple-kazhdan-kac-moody-lattices-exist: that supplies the finitely presented simple Kazhdan Kac–Moody lattices (Caprace–Rémy); this is a property of those with hyperbolic Weyl group.
artifacts:
  - research/artifacts/gq-bh-bh-lit-survey.md
---

**ESTABLISHED (2026-09-18)** through `hyperbolic-kac-moody-torsion-lf-proof`. Lane proof (bh-free-12), a short
combination of cited theorems, not independently reviewed. No priority is claimed.

## Statement

Let `A` be a generalized Cartan matrix whose Weyl group `(W, S)` contains no subgroup isomorphic to `Z^2`
(equivalently, by Moussong's theorem, `W` is word-hyperbolic). Let `Λ = G_A(F_q)` be the split minimal Kac–Moody group
over a finite field `F_q`.

1. Every finitely generated torsion subgroup of `Λ`, and of `Λ/Z(Λ)`, is finite.
2. **Finitely presented simple Kazhdan examples.** Take `A` in addition 2-spherical, indecomposable, non-spherical and
   non-affine, and `q > 1764^n`. Then `Λ/Z(Λ)` is finitely presented, simple and Kazhdan
   (`simple-kazhdan-kac-moody-lattices-exist`), and by item 1 it contains no infinite finitely generated periodic
   group. So it contains no infinite free Burnside group, no Tarski monster and no Grigorchuk group.
   - **Which Weyl groups qualify.** Reflection groups of compact hyperbolic Coxeter polytopes qualify whenever every
     `m_ij ∈ {2, 3, 4, 6}`, which is needed for a Kac–Moody root datum. They are 2-spherical and word-hyperbolic.
   - **Rank 3.** The compact hyperbolic triangle groups, e.g. `(2,4,6)`, which the 2-dimensional node also covers.
   - **Rank 4.** The cyclic Coxeter diagram with edge labels `3, 3, 3, 4` (non-adjacent pairs commuting) is recalled to
     be Lannér's compact hyperbolic tetrahedron `[(3^3,4)]`, not checked at source. Every triple of its generators is
     spherical (`A_3` or `B_3`), so its Davis building has dimension 3, which the 2-dimensional node does not reach.
3. **For Boone–Higman.** These finitely presented simple groups are not witnesses for
   `some-fp-simple-group-has-an-infinite-bounded-exponent-subgroup` and not hosts for
   `free-burnside-groups-satisfy-boone-higman`.

## Scope

- **Not covered:** Kac–Moody lattices whose `W` contains `Z^2` and a spherical triple of generators (building
  dimension `>= 3` and non-hyperbolic). For those, Haettel–Osajda's general conjecture (locally elliptic actions of
  finitely generated groups on finite-dimensional nonpositively curved complexes are elliptic) would be needed.
- Item 1 needs no finite presentation, simplicity or Kazhdan hypothesis. Item 2's rank-4 example rests on the recalled
  Lannér classification; the rank-3 example needs no such input.
