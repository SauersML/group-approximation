---
rg: 2
id: thompson-v-has-positive-rokhlin-entropy-action
kind: claim
title: Thompson's group V admits a free ergodic action of positive Rokhlin entropy
refuted_by:
  - thompson-v-nonsurjunctive
distinct_from:
  leavitt-unit-group-has-positive-rokhlin-entropy-action: that asks the same for the binary Leavitt unit group, which contains V and would give this claim; this is the a-T-menable subgroup V, which is not known to decide that one.
  thompson-v-surjunctive: that is surjunctivity of V, a topological statement; this is the measurable entropy statement that implies it through the self-copy dichotomy, with no converse known.
  thompson-v-is-sofic: that asks for sofic approximations of V, which would give this claim through sofic entropy; this could hold with V nonsofic.
artifacts:
  - research/artifacts/rokhlin-co-amenable-ascent-and-thompson-v-2026-09-12.md
---

**OPEN.** Some free ergodic p.m.p. action of Thompson's group `V = G_(2,1)` on a standard probability space has positive Rokhlin entropy.

**Equivalent forms.** `V` contains `V_[0] x V_[1] ~= V x V` and the cylinder permutation groups `Sym(2^n)`. By `rokhlin-supremum-dichotomy-with-centralized-self-copies`, `h^Rok_sup(V)` is `0` or `infinity`. So this claim is equivalent to each of:
- `h^Rok_sup(V) = infinity`;
- the uniform Bernoulli shift over `V` on any finite alphabet `A` has Rokhlin entropy `log |A|`;
- the Bernoulli 2-shift over `V` has positive Rokhlin entropy.

**Payoff.** It makes `V` surjunctive and `K[V]` directly finite for every field `K` (`thompson-v-surjunctive-via-positive-rokhlin-entropy`). Contrapositively, a strict automaton over `V` forces every free ergodic action of `V` to have Rokhlin entropy zero, so `thompson-v-nonsurjunctive` refutes this claim.

**Descent.** `leavitt-unit-group-has-positive-rokhlin-entropy-action` gives this claim (`thompson-v-positive-rokhlin-entropy-from-leavitt-units`).

## Attempts

- **Soficity.** A sofic `V` has maximal Bernoulli Rokhlin entropy, because sofic entropy bounds Rokhlin entropy from below. `thompson-v-is-sofic` is open, and every known lower bound for Rokhlin entropy runs through sofic entropy (Seward, arXiv:1501.03367v4, introduction).
- **Co-amenable induction (2026-09-12).** Unlike the Leavitt units, `V` is a-T-menable, so the obstruction `simple-kazhdan-groups-have-no-proper-co-amenable-subgroups` does not apply. `rokhlin-maximality-ascends-co-amenable-subgroups` would lift maximality from any infinite co-amenable subgroup. It gives nothing new here, for two reasons:
  - no point stabilizer of the Cantor action is co-amenable (`thompson-v-cantor-orbits-have-no-folner-sets`);
  - any subgroup known to be maximal is sofic, and a co-amenable sofic subgroup makes `V` sofic (Remarks 3-4 in Section 2 of the artifact).

  Along subgroups the question reduces to `thompson-v-is-sofic`.
- **Restriction and co-induction.** They give upper bounds only, as over the Leavitt units (Attempts of `leavitt-unit-group-has-positive-rokhlin-entropy-action`).
- **Tree and cube decompositions.** `V` acts properly on a CAT(0) cube complex, so FW fails, unlike over the Leavitt units. But no Bethe-type functional is an isomorphism invariant for a group with relations (`window-entropy-deficits-are-not-isomorphism-invariant`). The Bernoulli orbit relation is not treeable either, because `V ⊇ F_2 x F_2`. Farley and Gaboriau are mentioned here, not imported.
- **Koopman representation, weak containment, finitary witnesses.** These are blind in the same way as over every group. If `V` is not sofic, then, since `V` is simple, its sofic radical is all of `V`, and `sofic-radical-localizes-bernoulli-deficit-witnesses` gives no constraint.
- **What is left.** A lower-bound mechanism that uses no finite models and no subgroup induction, or a nonsofic maximal group sitting co-amenably inside `V`. None is known: Section 4 of the artifact.
