---
rg: 2
id: tree-lattices-hyperlinear-if-f2xf2-crossed-products-ce
kind: claim
title: If every crossed product of a p.m.p. action of F2 x F2 is Connes-embeddable, every torsion-free lattice in a product of two regular trees is hyperlinear
distinct_from:
  product-tree-lattices-in-paunescu-class-iff-f2xf2: that ties soficity of all actions of cocompact tree lattices to that of F2 x F2 through measure-equivalence invariance; this is the Connes-embedding analogue of one direction, proved by an explicit corner, and it concludes hyperlinearity of any torsion-free lattice.
  f2xf2-in-paunescu-class: that asks that every action of F2 x F2 be sofic, which implies the hypothesis here through the standard fact that essentially free sofic actions have Connes-embeddable crossed products; this uses only Connes embeddability of the crossed products and concludes hyperlinearity, not soficity.
  radu-bmw-lattice-sofic: that asks for soficity of one specific non-residually-finite lattice, and the graph routes it through the Paunescu class; this claim derives hyperlinearity of every torsion-free lattice in every product of two regular trees from crossed-product embeddability, and proves no soficity.
artifacts:
  - research/artifacts/fournier-facio-simple-factor-corner-2026-09-16.md
---

**ESTABLISHED** by route `tree-lattices-hyperlinear-if-f2xf2-crossed-products-proof`. Not
independently reviewed.

**Statement.** Let `a, b ≥ 3` and `H = Aut(T_a) × Aut(T_b)`. Let `S ≤ H` be a torsion-free
lattice, cocompact or not. Suppose that `L^∞(Y) ⋊ (F_2 × F_2)` is Connes-embeddable for every
p.m.p. action `F_2 × F_2 ↷ (Y, ν)`. Then `S` is hyperlinear.

**Contrapositive.** If some torsion-free lattice in some `Aut(T_a) × Aut(T_b)` is not
hyperlinear, then some **essentially free** p.m.p. action of `F_2 × F_2` has a
non-Connes-embeddable crossed product. The action is explicit: restrict the action of
`W_a × W_b` on `H/S` to a free finite-index subgroup, induce to `F_2 × F_2`, and multiply by a
Bernoulli shift. Here `W_a = C_2 * ... * C_2`, with `a` factors.

**Where it bites.**
- **Burger--Mozes.** It applies to every Burger--Mozes lattice. So a proof of
  `fournier-facio-simple-factor-not-hyperlinear` for a Burger--Mozes choice of the simple
  factor would produce a non-Connes-embeddable crossed product of `F_2 × F_2`.
- **Free groups.** For a free group in place of `F_2 × F_2`, every crossed product is
  Connes-embeddable. It is an amalgamated free product of hyperfinite algebras over `L^∞(Y)`
  (Brown--Dykema--Jung, not re-read here). So the product structure is the whole difficulty.
