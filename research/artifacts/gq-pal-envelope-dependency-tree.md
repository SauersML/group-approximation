# EnvelopeInput (T7's last hypothesis): dependency tree and feasibility (lane pal-envelope, 2026-09-19)

**Verdict:** EnvelopeInput cannot be proved in Lean without several major developments that
neither Mathlib nor this repo has. T7 (BFFHZ Question 3.1) should stay a conditional result and
leave the Palomar config, which admits only unconditional theorems.

## The statement

`GroupApproximation.BHPalomar.GraphProducts.EnvelopeInput` (GraphProducts/Reduction.lean) says:
for every faithful action `Γ ↷ S` of type (A), `Γ` embeds in some group `H` such that
`Aut_H(H ∗ F₂)` (`relAut H 2`) satisfies PBH. In BFFHZ (arXiv:2503.21882v2) this is:
- **Theorem C (i) ⇒ (iv):** a group with a type-(A) action embeds in a finitely presented simple
  MIF group `H`;
- **Theorem E, n = 2:** for a finitely presented simple MIF group `H`, `Aut_H(H ∗ F_n)` has a
  type-(A) action, namely its action on `Hom_H(H ∗ F_n, H) ≅ Hⁿ`.

## Dependency tree

1. **(i) ⇒ (ii)**: `Γ` embeds in a finitely presented simple twisted Brin–Thompson group `SV_Γ`.
   - 1a. The group `SV_Γ` and the embedding `Γ ↪ SV_Γ`. **Major**: this needs Brin–Thompson `nV`
     and its twisted versions, and the repo has neither. What it has is Higman–Thompson-type pieces:
     `HigmanThompson/BrownPresentation` (`brownF_isFinitelyPresented`) and `CompactCore`
     (`isSimpleGroup_commutator_compactCore`).
   - 1b. `SV_Γ` is simple (Belk–Zaremsky, *Twisted Brin–Thompson groups*). **Major.**
   - 1c. `SV_Γ` is finitely presented when the action is of type (A) (Zaremsky 2024).
     **Major**: this is the core finiteness theorem, proved with Brown's criterion on a
     Stein–Farley-type complex.
2. **(ii) ⇒ (iii) ⇒ (iv)**: `SV_Γ` is highly transitive, and a highly transitive simple group is
   MIF (Hull–Osin). **Major**: MIF for highly transitive groups needs Hull–Osin's argument.
3. **Theorem E** for a finitely presented simple MIF group `H`, acting on `Hom_H(H ∗ F₂, H)`:
   - 3a. Transitivity (BFFHZ Lemma 2.1). Elementary.
   - 3b. Faithfulness from MIF (Lemma 2.2). Elementary, given the definition of MIF.
   - 3c. Finitely many orbits on pairs; uses that `H` is infinite and simple (Prop. 2.3).
     Moderate.
   - 3d. Stabilizers are finitely generated (Prop. 2.6). Moderate to major.
   - 3e. `Aut_H(H ∗ F₂)` is finitely presented. **Major**: this needs a presentation of relative
     automorphism groups of free products (Fouxe-Rabinovitch / Gilbert type). Mathlib has
     `Coprod` and `FreeGroup` but no automorphism presentations. The repo has
     `Algebra/CoprodIFinitePresentation` (finite free products are finitely presented), which
     does not cover automorphism groups.

## No shortcut

- **The choice of `H` is forced.** `EnvelopeInput` needs an overgroup `H` of an *arbitrary*
  type-(A) group `Γ`, and constructing one is exactly Theorem C (i) ⇒ (iv). No fixed group
  already in the repo can serve, since `H` depends on `Γ`.
- **A direct route to `RetractAmalgamClosure` fails too.** Such a route would give
  `X *_C (C × K)` a type-(A) overgroup directly, without `relAut`. It would need a new finitely
  presented group with fg stabilizers and finitely many orbits on pairs. BFFHZ pose Question 3.1
  because no such construction is known.

## What would make T7 unconditional

Five formalizations, in bottom-up order:
- 1a, 1b and 1c: the twisted Brin–Thompson theory;
- 2: Hull–Osin;
- 3e: finite presentation of `Aut_H(H ∗ F₂)`.

3a–3d are feasible once those exist. Each of 1c and 3e is a multi-week Lean project on its own.

**Recommendation to the config owner (bh-pal-surface):** take T7 out of the Palomar config. Keep
`question31_of_envelopeInput` on main as a proved conditional theorem, with `EnvelopeInput` as
its only, clearly labelled, hypothesis.
