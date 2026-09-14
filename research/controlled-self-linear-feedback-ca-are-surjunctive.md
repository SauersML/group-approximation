---
rg: 2
id: controlled-self-linear-feedback-ca-are-surjunctive
kind: claim
title: Injective automata that peel block by block into self-linear rows are surjective
distinct_from:
  recipient-affine-three-factor-ca-are-surjunctive: that allows a pure-others offset in each row with a constant own coefficient, a class universal for Gottschalk's conjecture; this requires an ordering in which every offset vanishes with the earlier blocks, which makes surjunctivity provable over every group.
  certificate-controlled-routing-is-surjunctive: that routes each output datum from one input datum under a preserved certificate; this has no preserved certificate and lets every row combine its own block linearly under nonlinear control.
  central-c3-quadratic-surjunctivity-iff-direct-finiteness: that is same-track quadratic feedback on a central three-cycle, equivalent to direct finiteness; this allows own-block nonlinearity only when it vanishes with the earlier blocks, and needs no hypothesis on the group.
  common-factor-power-actor-ca-are-surjunctive: that is a same-track Boolean quadratic family; this has no same-block nonlinearity once the earlier blocks vanish.
artifacts:
  - research/artifacts/three-factor-audit-and-controlled-feedback-2026-09-12.md
---

Let `G` be any group and `R` a finite ring. Group the tracks into blocks
`X_1, ..., X_r`, block `a` with alphabet `R^(d_a)`, and let `F` be a cellular
automaton on the product full shift. Suppose that for every `a`, once
`X_1, ..., X_(a-1)` are set to zero, row `a` becomes

    X_a(g) + sum_(s in S) C_(a,s)(X_(a+1), ..., X_r)(g) . X_a(g s).

This row is linear in its own block. Its local controllers `C_(a,s)` are
`M_(d_a)(R)`-valued, may be arbitrarily nonlinear, and read only later blocks.
Suppose also that its constant part, the automaton obtained when all later
blocks vanish, is bijective.

If `F` is injective, then `F` is surjective.

**What a row may contain before the earlier blocks vanish.** A row may carry
pure-others offsets and nonlinearity in its own block, as long as these vanish
with the earlier blocks.

**Controlled self-linear feedback is the special case.** Every row is linear in
its own block under controllers reading the other blocks, and the constant
parts are invertible. This case satisfies the hypothesis in every ordering.

**Proof sketch.** Downward induction on the tail systems obtained by setting
the earlier blocks to zero. It runs through a two-block lemma, which straightens
one block with the certificate-fiber theorem and reads surjectivity off the
zero fiber.

**Scope.** The theorem contains the bipartite quadratic and target-multiplicative
theorems of the 09-08 block-elimination artifact. It extends them to
controllers, and vanishing offsets, of any degree and memory.

**Each hypothesis is sharp** (artifact section 3):
- Dropping invertibility of the constant parts admits every linear automaton,
  so Kaplansky's stable finiteness question for `R[G]`.
- An offset that survives in every ordering admits the universal
  recipient-affine normal form `(x + u, F(x) - x - u)`, whose first row carries
  an offset under both orderings. So this extension is all of Gottschalk's
  conjecture.
- Own-block nonlinearity that survives in every ordering admits the central
  three-cycle family, so direct finiteness in characteristic two.

A counterexample admits no presentation with a peeling order.

This is a class theorem. It does not prove Gottschalk's conjecture for any
group.
