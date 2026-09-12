---
rg: 2
id: stw99-problem-iv-kunneth-tensor-products
kind: claim
title: The Kunneth map is an isomorphism for nuclear A and torsion-free K-theory targets (STW Problem IV)
root: true
distinct_from:
  stw99-problem-ii-nuclear-uct: that is the full UCT; this is the a priori weaker Kunneth formula for tensor products, and the referee's example recorded by STW (reduced algebras of biexact Kazhdan groups, via Cuntz's K-amenability computations) shows the two genuinely differ outside the nuclear world.
artifacts:
  - research/artifacts/stw99-uct-cluster-2026-08-30.md
---

**Problem IV of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  For
separable nuclear `A` and separable `B` with `K_*(B)` torsion-free, is
`α : K_*(A) ⊗ K_*(B) → K_*(A ⊗ B)` an isomorphism?

By Schochet, a positive answer for all torsion-free targets yields the
Künneth short exact sequence for all `B`.  For nuclear algebras the
bootstrap classes for Künneth and UCT coincide, so the UCT implies this
(`stw99-uct-implies-kunneth`), but Künneth is a priori weaker: Skandalis's
UCT-failures `C*_r(G)` (biexact Kazhdan `G`) satisfy the Künneth formula.

## Attempts

Nothing beyond the bootstrap literature is recorded; the node is the
Künneth face of Problem II.  A counterexample must make `K_*(A ⊗ B)`
strictly larger than the algebraic tensor product against a torsion-free
target — no mechanism for this is known nuclearly; non-nuclearly the
referee's example shows the phenomena decouple from the UCT.
