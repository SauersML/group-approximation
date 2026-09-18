---
rg: 2
id: v-times-rigid-topologically-free-sft-full-groups-are-fp
kind: claim
title: "E3′: if a minimal topologically free SFT over a finitely presented group is quantum rigid, the full group of V times its transformation groupoid is finitely presented"
distinct_from:
  v-times-quantum-rigid-sft-full-groups-are-fp: that is P2′ for free SFTs, and it is the special case of this statement with free actions; this is the form the master route needs once freeness is relaxed, and unlike P2′ it has proved instances.
  topologically-free-subshift-full-groups-force-quantum-rigidity: that is the converse (finite presentation implies quantum rigidity and finite type) for topologically free actions, which is ESTABLISHED; this is the open sufficiency direction.
  v-times-tree-boundary-full-groups-are-f-infinity: that proves this statement, at level F_∞, for the end-shift scaffold over products of tree groups; this is the general statement.
  master-route-needs-only-topological-freeness: that shows the master-route implications use freeness only as topological freeness; this isolates the one finiteness premise that remains open on the group side.
---

**OPEN.** Gate E3′ of the topologically free form of Track A (lane bh-g3-topfree, 2026-09-18). The
route that consumes it is `boone-higman-via-v-times-rigid-topfree-sft-full-groups`.

## Statement

Let `Λ` be infinite and finitely presented, and `X ⊆ A^Λ` a nonempty minimal SFT on which `Λ` acts
**topologically freely**: `Fix_X(g)` has empty interior for every `g ≠ 1`. Suppose `X` is `D`-quantum
rigid over every field, for all large `D`. Then `F(G_V × (Λ ⋉ X)) = A(G_V × (Λ ⋉ X))` is finitely
presented.

No condition on isotropy is imposed. For the transformation groupoid, topological freeness is the
same as effectiveness and as essential principality.

## Relations

- **It contains P2′.** Free actions are topologically free, so this implies
  `v-times-quantum-rigid-sft-full-groups-are-fp`.
- **The converse holds.** Finite presentation forces quantum rigidity and finite type
  (`topologically-free-subshift-full-groups-force-quantum-rigidity`). So, among minimal topologically
  free subshifts over finitely presented groups, this statement says: fp ⟺ quantum rigid SFT.
- **Proved instances.**
  - Products of tree groups with the end-shift scaffold, at `F_∞`
    (`v-times-tree-boundary-full-groups-are-f-infinity`).
  - Cocompact type-rotating Ã₂ lattices, with a finite skew product of the chamber boundary, at `F_∞`
    (`a2-lattice-boundary-skew-shifts-are-quantum-rigid`, item 2, conditional on its host theorem).
  - Both are non-amenable. No instance of P2′ in the free form is known.
- **Everything downstream needs no freeness.**
  - `F = A`: `v-times-ample-full-groups-are-generated-by-transpositions` holds for every ample `H`.
  - Simplicity: Nekrashevych's Theorem 4.1 needs a minimal groupoid of germs, and `G_V × (Λ ⋉ X)` is
    one iff `Λ ↷ X` is minimal and topologically free.
  - Type (A): `fp-v-times-minimal-action-full-groups-have-type-a-actions` needs only minimality.
  - `Λ ↪ F`: needs faithfulness only.

## The Stein–Farley set-up needs only topological freeness

This audits Attempt 1 of `v-times-quantum-rigid-sft-full-groups-are-fp` (bh-g3-steinfarley).

| step of Attempt 1 | what it uses |
|---|---|
| cones `[u] × [P]_F`, elementary `C`-splits and `X`-splits, cube property | the pattern language only |
| infinitely many cone types over amenable `Λ` | invariant measure of full support; `X` has no isolated points (Cantor by `master-route-needs-only-topological-freeness`) |
| compression can make finitely many types over non-amenable `Λ` | the pattern language only |
| each element is, on each small cone, a prefix replacement times a translation `λ` | ampleness of `Λ ⋉ X` |
| **the translation label `λ` of a cone is unique** | **topological freeness**: if `λ` and `λ'` agree on a nonempty cylinder, then `λ^(-1)λ'` fixes an open set |
| finite cell stabilizers of the labelled partition complex | uniqueness of labels, plus finiteness of `{λ : λF = F'}` for finite `F, F'` |
| domain filtration, and the reduction to (A_N) and (B_N) | the items above |

So Attempt 1 and its reduction of P2′ to the uniform simple connectivity (A_N) apply verbatim to
topologically free `X`. Isotropy never enters the complex: a point stabilizer acts through
canonical similarities of the cones containing that point. The scaffold confirms this: its point
stabilizers are `Z^j`, and its full group is `F_∞`.

**Where freeness could still matter (not claimed either way).** Infinitely generated point
stabilizers in a rigid minimal topologically free SFT were not ruled out. Nothing in the set-up above
sees point stabilizers, and no mechanism is known by which one would block finite presentation.

## Lesson for general BH

The group side of Track A never needs a free SFT: every step downstream of finite presentation needs
only a minimal effective action, and the one open finiteness step has an audit showing that its
proof set-up uses freeness only as uniqueness of local translation labels. So the correct gate is
this topologically free E3′. It is the first form of the gate with proved instances, and both
instances are boundary (compression) codings over non-amenable groups.
