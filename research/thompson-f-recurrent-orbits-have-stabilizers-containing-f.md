---
rg: 2
id: thompson-f-recurrent-orbits-have-stabilizers-containing-f
kind: claim
title: "Whenever a finitely generated group containing F has a recurrent orbit, the point stabilizer meets that copy of F in a subgroup containing a copy of F"
distinct_from:
  f-dyadic-action-is-not-recurrent: that proves the dyadic F-set is transient; the dyadic stabilizers already contain F, so this theorem does not decide that case. This theorem forbids recurrence on every F-set whose stabilizers contain no copy of F, in every host group.
  thompson-f-dyadic-action-is-extensively-amenable: that is the open extensive amenability of one action; this shows that no recurrent action of any group containing F can have F-free stabilizers, so recurrence plus amenable stabilizers never proves amenability without already knowing it for a group containing F.
  every-subgroup-of-thompson-f-is-ea-or-contains-f: that is the open Brin–Sapir dichotomy for subgroups of F; this proves, unconditionally, that stabilizers of recurrent F-orbits sit on the "contains F" side.
  thompson-f-end-rigid-schreier-graphs-are-amenable: that concerns amenability of Schreier graphs; this concerns recurrence, which is stronger than amenability for Schreier graphs, and draws a conclusion about stabilizers rather than graphs.
---

**ESTABLISHED.** **Theorem R.** Let `G` be a finitely generated group acting on a set
`X`, and let `x ∈ X` be a point whose orbit `G·x` is recurrent. By
`recurrent-orbits-force-every-z3-to-meet-the-stabilizer` this does not depend on the
generating set. Then for every subgroup `F_0 ≤ G` with `F_0 ≅ F`, the group
`G_x ∩ F_0` contains a subgroup isomorphic to `F`.

**Corollaries.**
1. Every transitive `F`-set with a recurrent Schreier graph has point stabilizers
   containing a copy of `F`. Equivalently, `F/H` is transient whenever `H ≤ F`
   contains no copy of `F`. Examples include `H` abelian, solvable, residually
   finite, or of locally subexponential growth.
2. **(Kill of the recurrence method.)** The recurrence route to amenability (a
   recurrent action is extensively amenable, and an extensively amenable action with
   amenable stabilizers gives an amenable group; Juschenko–Nekrashevych–de la Salle,
   Juschenko–Matte Bon–Monod–de la Salle) can prove amenability of a finitely
   generated group `G ⊇ F` only through stabilizers `G_x` that again contain `F`.
   - This holds for every host `G`: `F` itself, `T`, `V`, any finitely generated full
     group or automaton group into which `F` embeds.
   - It holds for every `G`-set `X` and every recurrent orbit, not only the dyadic
     action.
   - *Invariant:* "contains a subgroup isomorphic to `F`".
   - *Where every member dies:* the stabilizer step. The input "`G_x` is amenable" is
     at least as hard as amenability of `F`, since `G_x ⊇ F` and amenability passes to
     subgroups.

**Scope.**
- The theorem is about recurrence, not extensive amenability. Extensive amenability
  proved by non-recurrent means is untouched. So is the germ-groupoid form of the
  JNdlS criterion, where the amenability input is a groupoid of germs rather than
  `G_x`.
- For `F ↷ D` the stabilizers contain `F` and the action is transient, so there is
  no conflict with `f-dyadic-action-is-not-recurrent`.
- No priority is claimed; the argument is short and may be known.

Proof route: `thompson-f-recurrent-orbits-stabilizers-contain-f-proof`. Used by
`f-free-groups-are-closed-under-recurrent-extensions`.
