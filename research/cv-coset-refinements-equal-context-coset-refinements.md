---
rg: 2
id: cv-coset-refinements-equal-context-coset-refinements
kind: claim
title: A perfect trace of a Boolean constraint system lifts through a coset refinement of its constraint-variable game iff through one of its context game, so hidden labels on variable questions import the forbidden-pair split
distinct_from:
  cv-coset-refinements-are-edge-label-coset-systems: that is the normal form of a single refinement of the constraint-variable game; this compares the two presentations and shows that they lift the same perfect traces.
  forbidden-pair-splits-are-central-rectangle-splittings: that shows every perfect trace of the constraint-variable game passes that game's own (RCS) conditions; this shows that lifting through its coset refinements still imposes the forbidden-pair split on the source game.
  hidden-labels-import-cross-context-commutation: that proves the three-context split for refinements of context games; this transfers the split to refinements of constraint-variable games, where its direct form is vacuous because the far neighbours are single variables.
---

**ESTABLISHED** by `cv-coset-refinements-equal-context-coset-refinements-proof`.
Not reviewed by an ex-verify lane.

**Setting.**
- `B` is a finite Boolean constraint system.
- `G_B` is its context game, as in `exact-label-coset-refinements-are-affine`.
- `G_cv(B)` is its constraint-variable game, as in
  `cv-coset-refinements-are-edge-label-coset-systems`.
- Coset refinements are as in
  `coset-refinement-forces-rectangular-central-splitting`, with any groups, any
  padding, and relations on every pair.
- A perfect trace `tau` of `B` *lifts through* a refinement `R` if some tracial
  state on `A(R)` pulls back to `tau` along the pushforward `A(B) -> A(R)`.

**Theorem.**
- **(EQ1) From constraint-variable to context.**  Suppose `R` refines `G_cv(B)`
  and `A(R) != 0`.  Then there is a coset refinement `R^ctx` of `G_B` with the
  same context groups and padding, and a unital *-homomorphism `A(R^ctx) -> A(R)`
  that is the identity on context PVMs.
  - For `v in c ∩ c'`, the relation of `R^ctx` on `(c,c')` is carried by a
    *transit label*.
  - A transit label is a PVM that is at once a coarse-graining of `p_c`, of
    `p_(c')` and of `p_v`, and that refines `X_v`.
- **(EQ2) From context to constraint-variable.**  Every coset refinement
  `R^ctx` of `G_B` gives a coset refinement `R^cv` of `G_cv(B)`, and a unital
  *-homomorphism `A(R^cv) -> A(R^ctx)` that is the identity on context PVMs.  The
  variable question `v` copies the PVM of a designated context `c_v ∋ v`.
- **(EQ3) Consequence.**  A perfect trace of `B` lifts through some coset
  refinement of `G_cv(B)` iff it lifts through some coset refinement of `G_B`.

**Corollary (one-hot/NAND sources).**  Let `B = B(G)` be the one-hot/NAND
presentation of a synchronous game `G`, as in Corollary 2 of
`hidden-labels-import-cross-context-commutation`.  An example is
`B_I` of `perfect-qc-separation-yields-finite-bcs-with-no-matrix-model`.
- **(RCS) is forced on `G`.**  Suppose a perfect trace lifts through a coset
  refinement of `G_cv(B)`, allowing hidden labels on the variable questions and
  relations between non-incident questions.  Then every pair algebra
  `W*(P_q, P_(q'))` of `G` satisfies (RCS) of
  `coset-refinement-forces-rectangular-central-splitting`.
- **Factor pair algebras.**  If such a pair algebra is a factor, then for each
  forbidden pair, one of `P_q^a`, `P_(q')^(a')` is `0` or `1`.
- **The binding conditions.**  Every pair algebra of `G_cv(B)` that carries a
  forbidden pair is abelian (Corollary 3 of
  `forbidden-pair-splits-are-central-rectangle-splittings`), so that game's own
  (RCS) conditions always pass.  They are not the conditions that bind.
  Switching the source to the constraint-variable game does not evade the split
  on `G`.

**What this decides.**
- **Readouts on the variable questions.**  Readout systems with non-homomorphic
  readouts on the variable questions (the hidden labels of the normal form) lift
  exactly the same perfect traces as hidden labels in context syntax.
- **What stays open.**
  - The constraint-variable presentation opens no new region.
  - A lift of a trace of `B_I` in either presentation needs (RCS) on every
    question pair of the independent-set game `I`.
  - Whether some perfect trace of `B_I` lifts at all is the context-syntax
    problem.  It is not decided here.

**Model tests.**
- **The magic square.**
  - Its label-exact refinement in constraint-variable syntax (`Z_2` labels,
    identity readouts) gives, by (EQ1), the linear-system context game.
  - Conversely, (EQ2) sends that context game back to a refinement in
    constraint-variable syntax.
  - Both algebras are nonzero.
- **A factor model.**  Take the model of
  `hidden-labels-import-cross-context-commutation`:
  - `c = {u,w}` with NAND, `c' = {u,y}`, `c'' = {w,z}`;
  - `M_3` with its normalized trace.

  Every pair algebra of `G_cv(B)` that carries a forbidden pair is abelian.  Yet
  by Corollary 1 of that node and (EQ1), this trace lifts through no coset
  refinement of `G_cv(B)`.
- **Classical solutions.**  Every classical solution lifts in both presentations,
  with trivial groups.
