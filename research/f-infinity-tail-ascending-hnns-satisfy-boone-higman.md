---
rg: 2
id: f-infinity-tail-ascending-hnns-satisfy-boone-higman
kind: claim
title: Last-section ascending HNN extensions inside bounded automata groups satisfy Boone–Higman whenever their tail group is of type F_infinity, through a one-point germ extension of a Röver–Nekrashevych group
distinct_from:
  bounded-last-section-ascending-hnns-satisfy-boone-higman: that needs finite and eventually finitary first sections, so that the host is a contracting Röver–Nekrashevych group; this allows infinite first sections (tail group any F_infinity group, e.g. Z^2) and uses a finite germ extension host instead, so it covers dilation-type examples such as the Basilica.
  last-section-ascending-hnns-embed-in-rover-nekrashevych-groups: that is the embedding lemma with no host finiteness; this proves the host has type F_infinity and embeds in a finitely presented simple group.
  bhm-singfix-condition-forces-fp-germ-groups: that is a necessary condition on germ groups; this is a sufficient criterion for germ groups that are ascending HNN extensions, a case outside the hypotheses of Belk–Hyde–Matucci Corollary cor:MainFinitenessCorollary.
---

**ESTABLISHED** (lane proof `last-section-f-infinity-tail-bh-proof`; not reviewed; no priority
claimed, bounded search in Scope).

## Statement

Let `d ≥ 2`, `L = d−1`, `S ≤ Aut(T_d)` a bounded automata group (BHM sense: finitely
generated, self-similar, each element with finitely many singular rays). Let `G ≤ S` be
finitely generated and `σ: G → G` an endomorphism with

```text
σ(g) = (ψ_0(g), …, ψ_{L−1}(g), g),      ψ_z(G) ≤ S   (z < L).
```

Assume (H0): the ray `0^∞` is not directed for `S`, i.e. every state `q` of a finite
automaton generating `S` has `q|_{0^n} = 1` for large `n`. This holds for all instances below.

Define the **tail group** `E(G)` as the image of `G` under
`g ↦ (ψ_z σ^k(g))_{k ≥ 0, z < L}` in `∏ S`. If `E(G)` has type `F_∞`, then:

1. `G*_σ` embeds in a group `W` of type `F_∞`. `W` is the full closure of `⟨V_d S, ĝ, s⟩`
   (hats and the Thompson element `s` of the embedding lemma). It is a finite germ extension of
   `V_d S` whose singular set is the single `V_d`-orbit `O` of `0^∞`. Its germ group there is
   the ascending HNN extension `E(G)*_{σ̄}` of the tail group, i.e. the direct limit of
   `E(G) →σ̄ E(G) → …` extended by `Z`.
2. `W` acts faithfully and highly transitively on the `V_d`-orbit `O_q` of a suitable rational
   point `q`, with stabilizers of finite subsets of type `F_∞`. So `SV_W` is a finitely
   presented simple group containing `G*_σ`
   (Zaremsky's theorem as quoted in BBMZ arXiv:2309.06224, `thrm:action_to_simple`), and
   `G*_σ` satisfies **Boone–Higman** and lies in the **permutational class** `B_A`.

## Instances

- **Finite tails.** If each `ψ_z(G)` is finite, `E(G)` is finite. This covers
  `bounded-last-section-ascending-hnns-satisfy-boone-higman` without its eventual-finitary
  condition: Grigorchuk–Lysenok, the Grigorchuk supergroup, Fabrykowski–Gupta.
- **Abelian tails.** If the `ψ_z` take values in an abelian subgroup, `E(G)` is a quotient of
  `G^{ab}`, so it is finitely generated abelian, hence `F_∞`.
  - The **Basilica** extension along `a ↦ b², b ↦ a` has tail `Z²`. It is the
    Bartholdi–Virág finitely presented amenable group that is not subexponentially amenable:
    `basilica-fp-amenable-hnn-satisfies-boone-higman`.
  - Calibration: the odometer `τ` with `σ(τ) = τ²` has tail `Z` and gives `BS(1,2)`. That case
    is known.

## Lesson for general BH

An ascending HNN extension costs a Thompson-like host exactly **one new singular orbit**.
- The stable letter is a single element of `F` (a ray shift).
- The whole difficulty moves into the germ group at one rational point. That germ group is
  again an ascending HNN extension, of the much smaller tail group `E(G)`.

Belk–Hyde–Matucci's germ-extension finiteness theorem asks the base germ group to be normal or
of finite index. Here it is neither: the dilation germ acts on `Z[1/2]²` by an expanding matrix
for Basilica. The transferable fix is to run BHM's Appendix A stabilizer proof with the tail
group carried along. When the germ group is an ascending HNN extension of an `F_∞` group that
lifts equivariantly into the attracting cone, every SingFix group is an iterated ascending
HNN extension of `(Fix of a Röver–Nekrashevych group) × E(G)^m`, so it is `F_∞`.
This gives a **closure principle**: BH-type hosts absorb ascending HNN extensions whose tail
dynamics is `F_∞`.

## Scope

- BHM arXiv:2407.03149v1 (TeX read at `$GQ/src/bhm/bhm-2407.03149v1.tex`):
  - Theorem `thm:SingFixFiniteness`;
  - Theorem `thm:RoverNek` (`V_{d,r}S` of type `F_∞` for bounded `S`, all `r`);
  - Theorem `thm:Stabilizers` and its proof (Appendix A), whose induction is reused.
- BBMZ arXiv:2309.06224: `thrm:action_to_simple` and `prop:HighlyTransitiveAction`.
- Priority: BHM's TeX mentions HNN extensions only in Appendix A; neither BHM nor BBMZ treats
  ascending HNN extensions of bounded groups. No MathSciNet search.
