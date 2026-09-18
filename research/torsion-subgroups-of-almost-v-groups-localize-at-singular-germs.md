---
rg: 2
id: torsion-subgroups-of-almost-v-groups-localize-at-singular-germs
kind: claim
title: A finitely generated torsion group of Cantor homeomorphisms that are locally in V off finite sets either has infinite orbits on its singular support, or is locally-finite-by-(germs at finitely many fixed points); an infinite simple one then embeds in a single singular germ group
distinct_from:
  almost-v-fw-subgroups-act-through-finitely-many-germs: that proves the germ reduction for FW groups, where FW forces a finite singular orbit after conjugation; this is the torsion version, where finiteness of the singular orbit is the whole question and is not automatic, since torsion groups need not have FW.
  simple-kazhdan-in-germ-extension-of-v-sits-in-one-germ-group: that locates infinite simple Kazhdan subgroups in one germ group; this locates infinite simple torsion subgroups (Ol'shanskii-type bounded-exponent simple groups, Tarski monsters) in one germ group, under the finite-orbit alternative.
  fp-simple-groups-have-residually-finite-torsion: that is the uniform torsion separator (RT) and its census; this is the localization tool for its shell-route row, showing where a finite germ extension must carry non-residually-finite torsion.
artifacts:
  - research/artifacts/gq-bh-bh-lit-survey.md
---

**ESTABLISHED (2026-09-18)** through `almost-v-torsion-localization-proof`. Lane proof (bh-free-12), elementary,
not independently reviewed. No novelty is claimed. It is the torsion analogue of the FW germ reduction.

## Setting

As in `almost-v-fw-subgroups-act-through-finitely-many-germs`:
- `C = {0,1}^N` and `V` is Thompson's group.
- `sing(g)` is the set of points where the homeomorphism `g` is not locally equal to an element of `V`.
- `𝐇 = {g ∈ Homeo(C) : sing(g) finite}`. It contains every finite germ extension of `V` (Belk–Hyde–Matucci), `VA`,
  and every shell group `E_ν`.
- `𝒢_y` is the group of germs at `y` of homeomorphisms fixing `y`.

Let `T = ⟨S⟩ ≤ 𝐇` be finitely generated and torsion, and put `Σ = T · ⋃_{s ∈ S^{±1}} sing(s)`.

## Statement

1. **Support.** `Σ` is `T`-invariant and `sing(t) ⊆ Σ` for every `t ∈ T`.
2. **Finite singular orbit.** Suppose `Σ` is finite. Let `T_1` be the pointwise fixer of `Σ` in `T`, a normal
   subgroup of finite index. Then the germ homomorphism `φ : T_1 → ∏_{y ∈ Σ} 𝒢_y` has kernel contained in `T_1 ∩ V`, hence
   locally finite. Hence:
   - (a) if every germ image `[T_1]_y` is finite, then `T` is finite;
   - (b) `T_1 / ker φ` embeds in the finite product `∏_{y ∈ Σ} [T_1]_y` of finitely generated torsion groups;
   - (c) if `T` is infinite and simple, then `T` fixes `Σ` pointwise, and for some `y ∈ Σ` the germ map
     `T → [T]_y` is injective. So `T` embeds in the isotropy germ group `(E)_y` of every `E ≤ 𝐇` containing it.
3. **Dichotomy.** If `T` is infinite, then either
   - (i) `Σ` is finite, and some singular germ image `[T_1]_y` is an infinite finitely generated torsion group; or
   - (ii) `Σ` is infinite: `T` has an infinite orbit on the singular points of its own elements.

## Lesson for general BH

In every finite germ extension of `V` (shell, `VA` and germ-engine hosts), infinite torsion can enter in only two
ways:
- **through singular germs at finitely many fixed points.** For a simple bounded-exponent input it sits inside one
  germ group, and that germ group is finitely presented whenever Belk–Hyde–Matucci Theorem 2.1 certifies the host
  (`bhm-singfix-condition-forces-fp-germ-groups`);
- **by moving singular points along infinite orbits.**

The second is the dynamical form of the freedom that Burnside groups really have. They act without fixed point on
infinite-dimensional CAT(0) cube complexes (Osajda, as recalled in Norin–Osajda–Przytycki arXiv:1902.02457 §1), while
FW or Kazhdan inputs are forced into alternative (i) (`almost-v-fw-subgroups-act-through-finitely-many-germs`).

So for the shell route the Burnside test splits cleanly. Kazhdan torsion inputs, e.g. infinite Burnside quotients of
hyperbolic Kazhdan groups, must be carried by finitely presented germ groups. Non-FW torsion inputs may instead use
infinite singular orbits, and no obstruction to that is known.
