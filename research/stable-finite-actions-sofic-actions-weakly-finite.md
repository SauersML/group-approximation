---
rg: 2
id: stable-finite-actions-sofic-actions-weakly-finite
kind: claim
title: If a group is stable in finite actions, each of its sofic p.m.p. actions is weakly contained in finite actions
distinct_from:
  sofic-stable-implies-residually-finite: that uses stability in finite actions to force residual finiteness of a sofic group; this carries stability from limit actions of sofic approximations to every Paunescu-sofic standard action
  stable-finite-actions-blocks-codense-kazhdan-coset-soficity: that is an obstruction to soficity of coset actions of codense Kazhdan pairs; this is the general transfer to all sofic standard actions, with no hypothesis on the action
  alekseev-thom-stability-finite-actions-boundary: that records Alekseev--Thom's residual amplification lemma and the open literature boundary; this is a transfer statement proved here from Paunescu's definition
artifacts:
  - research/artifacts/f2xf2-finite-action-stability-dichotomy-2026-09-16.md
---

Let `Γ` be a countably infinite group that is stable in finite actions (Gohla--Thom Definition 3.7).

1. Let `a = Γ ↷ (X, μ)` be a p.m.p. action on a standard probability space that is sofic in Păunescu's sense
   (Definition 1.4). Then `a` is weakly contained in the family `F(Γ)` of finite `Γ`-actions.
2. Hence an action `a` on a standard space with `a ⊀ F(Γ)` is not sofic.
3. If moreover `Γ` is residually finite, then `a × (Γ ↷ Γ̂)` is also not sofic. Here `Γ̂` is the profinite
   completion with Haar measure. This product is a free p.m.p. action on a standard nonatomic space.
   If `Γ` is not finitely generated, read `Γ̂` as `lim Γ/N_i` along a decreasing chain of finite-index
   normal subgroups with `∩ N_i = 1`, so that the space stays standard.

*Proof.* See artifact §2 (Proposition A) and §3 (Corollary B). The proof is internal.

* **Lifting.** A Păunescu embedding lifts projections of `L^∞(X)` to sets (functional calculus,
  threshold `1/2`) and group unitaries to permutation sequences. The permutations are asymptotically
  multiplicative, and asymptotically free by trace preservation.
* **Statistics.** Ultralimits of set statistics recover `μ(E ∩ gE')`.
* **Diagonal choice.** Diagonal indices along a dense sequence of sets give a sequence sofic approximation.
  Its limit action carries Loeb sets with exactly these statistics, so `a ≺` limit action `≺ F(Γ)`.
* **Part 3.** `a` is a factor of `a × Γ̂`, and weak containment is transitive.

*Trust surface.* The only external input is Definition 3.7 itself, read with the Loeb limit-action
convention of artifact §1. The statistics used converge as honest limits, so the choice of free
ultrafilter does not matter.

Gohla--Thom §3.1 print sofic approximations only for finitely presented `Γ`, as free-group
homomorphisms, with limit actions as metric ultraproducts of measure algebras. Alekseev--Thom
(arXiv:2512.15494, Definition 3.1) state the property for countable groups. Artifact §1 checks that
the conventions agree where both apply. Both routes that consume this claim apply it to `F_2 × F_2`, which is finitely presented.

The level is folklore and no novelty is claimed.

* Gohla--Thom (arXiv:2403.09582v2, Remark 3.14 and Corollary 3.15) use the transfer implicitly for
  Elek--Lippner soficity, read as weak containment in a limit action. What is written out here is the
  passage from Păunescu's crossed-product definition to that form.
* The same mechanism appears inline, for microstates, in
  `sl3z-cocompact-nonsofic-from-stability-and-no-finite-approx`.
