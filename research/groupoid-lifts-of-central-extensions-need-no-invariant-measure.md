---
rg: 2
id: groupoid-lifts-of-central-extensions-need-no-invariant-measure
kind: claim
title: An odometer-type lift of a central Z-extension over a compact action forces its real class to vanish whenever the action has an invariant probability measure
distinct_from:
  odometer-lift-central-extensions-of-v-subgroups-into-2v-tau: that is the positive lift lemma (a locally constant trivialization on the action groupoid gives an embedding into 2V_tau); this is a necessary condition for any such trivialization, and applies to every compact action, not only to subgroups of V.
  kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf: that constrains Kazhdan subgroups of whole full groups of amenable-orbit actions; this constrains only lifts of the specific cocycle form, but for every group with a real-nontrivial central extension, Kazhdan or not.
---

**ESTABLISHED** (lane proof, elementary, not reviewed). No priority claimed.

## Statement

Let `Q` act on a compact Hausdorff space `Y` by homeomorphisms, and let
`1 → ⟨z⟩ → Q̃ → Q → 1` be a central extension with `z` of infinite order and class
`c ∈ H^2(Q; Z)`. Suppose `Q̃` acts on `Z × Y` by

    q̃ · (m, y) = (m + k(q̃, y), q y),        z · (m, y) = (m + d, y),  d ≠ 0,

with each `k(q̃, ·) : Y → Z` continuous. Call this a **lift over `Y`**. This is the
form produced by `odometer-lift-central-extensions-of-v-subgroups-into-2v-tau`, after
restricting from `Z_2` to the dense subset `Z`. If `Y` carries a `Q`-invariant Borel
probability measure, then `c` maps to `0` in `H^2(Q; R)`.

## Proof

Choose a normalized section `q ↦ q̃`, and let `ε` be the cocycle
`q̃ q̃' = z^{ε(q,q')} \widetilde{qq'}`. Put `κ(q, y) = k(q̃, y)`. The action law and the
central translation give

    d·ε(q,q') + κ(qq', y) = κ(q', y) + κ(q, q'y)      for all q, q', y.

Each `κ(q, ·)` is continuous into `Z` on a compact space, so it is bounded and Borel.
Let `μ` be the invariant measure, and put `φ(q) = ∫ κ(q, y) dμ(y)`. Integrating, and
using `∫ κ(q, q'y) dμ = φ(q)` by invariance,

    d·ε(q,q') = φ(q) + φ(q') − φ(qq').

So `d·ε` is a real coboundary, and `c_R = 0` since `d ≠ 0`. ∎

## Consequences

1. **Equicontinuous models never lift real-nontrivial classes.** An inverse limit of
   finite `Q`-sets carries an invariant probability measure: take a limit of
   normalized counting measures. This covers every self-similar, rooted-tree,
   profinite or odometer-type action. So the lift mechanism cannot run on the Cantor
   actions behind the residually finite hosts of main.
2. **Amenable quotients.** If `Q` is amenable, every compact `Q`-space has an
   invariant probability measure. So a central extension of an amenable group with
   `c_R ≠ 0` has no lift over any compact `Q`-space. Example: the Heisenberg group
   `H_3(Z)`, a central extension of `Z^2` whose class is nonzero over `R`.
3. **Deligne's lattice.** For `Γ = Sp_{2n}(Z)` with `n ≥ 2`, the class of the
   preimage `Γ̃` in the universal cover of `Sp_{2n}(R)` is nonzero in `H^2(Γ; R)`. It
   is the Kähler/Hodge class. This is textbook (Borel), not read at source here. So a
   lift of `Γ̃` needs a compact `Γ`-space with **no** invariant probability measure.
   `deligne-extension-dies-on-lagrangian-cantor-covers` supplies such spaces: Cantor
   covers of the real Lagrangian Grassmannian, which carries no `Γ`-invariant
   probability measure.

## Calibration

`T̄ → T` has nonzero real Euler class (Ghys–Sergiescu, textbook). Its lift over the
Cantorized circle exists (`odometer-lift-central-extensions-of-v-subgroups-into-2v-tau`),
and `T` preserves no probability measure on the circle: already `PSL_2(Z) ≤ T` does
not. So the obstruction and the construction are consistent.

## Scope

This is about lifts of the displayed cocycle form only, where the centre acts purely
by translation on a separate coordinate. It does not say that `Q̃` fails to embed in
a group such as `2V_τ` in some other way.
