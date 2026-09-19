---
rg: 2
id: thompson-f-recurrent-germ-criteria-return-f-as-an-input
kind: claim
title: "In every recurrent germ-groupoid criterion (JNdlS Theorem 3.1) applied to any group of homeomorphisms containing F, F′ fixes all singular orbits, and either a germ group or the full group [[H]] contains a copy of F"
distinct_from:
  thompson-f-recurrent-orbits-have-stabilizers-containing-f: that puts a copy of F into stabilizers G_x of recurrent orbits; JNdlS's amenability inputs are germ groups, which are quotients of stabilizers and can kill F, and the full group [[H]]. This theorem covers those inputs, which that file's scope leaves open.
  f-functor-cocycles-need-an-exotic-recurrent-action: that kills the JMMS functor-cocycle method; this kills the JNdlS germ-groupoid criterion, whose amenable piece is [[H]] with an arbitrary groupoid H, not a functor image.
  thompson-f-point-orbits-are-transient: that kills the germ route only for F's own actions on [0,1] and on the Cantor set; this covers every host group G ⊇ F, every space X and every groupoid H.
  thompson-f-recurrent-f-sets-factor-through-the-abelianization: that is the statement about recurrent F-sets used here as input; this converts it into a kill of the germ-groupoid criterion via simplicity of F′ and the dichotomy on germs.
  thompson-f-does-not-embed-in-wobbling-groups-of-recurrent-graphs: that transfers the abelian-factor theorem to wobbling groups; this transfers it to germ groupoids and topological full groups.
---

**ESTABLISHED** by `thompson-f-recurrent-germ-criteria-proof`. It is conditional on
`thompson-f-recurrent-f-sets-factor-through-the-abelianization`, which is ESTABLISHED but not yet
refereed.

**Setting.** This follows `jndls-recurrent-groupoid-extension-theorem`.
- `G` is a finitely generated group of homeomorphisms of a topological space `X`.
- `H` is a groupoid of germs of homeomorphisms of `X` whose full group `[[H]]` is a group.
- A point `x` is *singular* if `(g,x) ∉ H` for some `g ∈ G`. `V` is the union of the `G`-orbits of the
  singular points.
- `𝒢_x` is the germ group at `x`, that is, the stabilizer of `x` in `G` modulo the elements that are
  trivial near `x`.
- Assume condition (3) of JNdlS Theorem 3.1: `Γ(x,G)` is recurrent for every singular `x`.

Condition (2) is not needed.

**Theorem G.** Let `F_0 ≤ G` with `F_0 ≅ F`.
1. `F_0′` fixes `V` pointwise.
2. Exactly one of the following holds.
   - **(A)** For some `v ∈ V` the germ map `F_0′ → 𝒢_v`, `k ↦ (k,v)`, is injective. Then `𝒢_v`
     contains a copy of `F`.
   - **(B)** Every `k ∈ F_0′` is the identity near every point of `V`. Then
     `F_0′ ≤ G ∩ [[H]]`, so `[[H]]` contains a copy of `F`.

**Corollary 1 (class kill: the germ-groupoid form of the recurrence method).**
- *Scope.* Theorem 3.1 of Juschenko–Nekrashevych–de la Salle, and hence its compact special case
  Theorem 1.1, can prove amenability of a group containing `F` only if one of its amenability
  inputs already contains `F`.
  - This holds for every host `G ⊇ F` (`F`, `T`, `V`, any finitely generated full group or automaton
    group), every space `X` and every groupoid `H`.
  - The input that contains `F` is either (1), amenability of `[[H]]`, or (4), amenability of a germ
    group at a point of a singular orbit.
- *Invariant.* "Contains a subgroup isomorphic to `F`".
- *Where every member dies.* At the input step, (1) in case (B) and (4) in case (A). That input is at
  least as hard as `thompson-f-is-amenable`.

**Corollary 2 (a transience theorem for all hosts).** Let `G ⊇ F` and `H` be as in the Setting, but
without assuming (3). Suppose neither `G ∩ [[H]]` nor any germ group `𝒢_x` contains a copy of `F`.
Then some orbit of a singular point is transient.

**Sanity check.** Take `G = F ↷ [0,1]` and let `H` be the germs of homeomorphisms that are affine
near their origin.
- The singular points of the generators are their breakpoints, so (2) holds.
- `[[H]]` consists of the affine homeomorphisms of `[0,1]`, so it is finite and (1) holds.
- The germ groups of `F` are subgroups of `Z²`, so (4) holds.
- By Corollary 2, (3) must fail. It does: the singular points are dyadic and the dyadic orbit is
  transient (`f-dyadic-action-is-not-recurrent`).

So recurrence is the only hypothesis this kill uses, and it cannot be dropped.

**Scope.**
- *Not covered.* Extensive amenability of the singular set proved without recurrence, as in
  Juschenko–Matte Bon–Monod–de la Salle. For `F ↷ D` this is the flagship itself
  (`thompson-f-amenable-via-dyadic-extensive-amenability`).
- *Also not covered.* Analytic routes.
- No priority is claimed.
