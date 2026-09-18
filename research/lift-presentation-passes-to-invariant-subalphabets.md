---
rg: 2
id: lift-presentation-passes-to-invariant-subalphabets
kind: claim
title: If every state preserves a sub-alphabet and relators of the restricted automaton lift, a finitely generated lift ideal restricts to a finitely generated lift ideal, so V_{|X|}(G) finitely presented implies V_{|W|} of the restriction finitely presented
distinct_from:
  loop-retraction-forces-fp-eventual-section-groups: that retracts onto the sections at one letter fixed by every state and concludes finite presentation of the eventual section group; this retracts onto the action on an invariant sub-alphabet and concludes lift-presentation of the restricted action, which can hold without finite presentation.
  lift-presentable-groups-closed-under-products-and-wreaths: that builds lift-presented actions from smaller ones (products, finite wreaths); this goes the other way, from a lift-presented action to the action on an invariant sub-alphabet, and records that the converse fails.
  finitary-extensions-preserve-lift-presentability: that adds states above a lift-presented sub-automaton; this removes letters below one.
---

**ESTABLISHED** by `lift-presentation-passes-to-invariant-subalphabets-proof` (lane proof by
bh-free-02, elementary, not independently reviewed; no priority claimed). The statement about lift
ideals uses nothing beyond the definitions. The translation into finite presentation of
Röver–Nekrashevych groups uses both halves of Theorem A of
`rover-nekrashevych-fp-iff-finite-lift-presentation`.

## Setting

Notation of `rover-nekrashevych-fp-iff-finite-lift-presentation`:
- `S <= Aut(X^*)` is finite and closed under sections and inverses, `F = F(S)`, and
  `N = ker(F -> G)`.
- `W ⊆ X` with `|W| >= 2` and `s(W) = W` for every `s in S`.

Each state then preserves `W^*`. Write `s̄` for its restriction, `S̄ = {s̄}`, and `Ḡ = ⟨S̄⟩ <= Aut(W^*)`.
Then `S̄` is closed under sections at `W`-letters and under inverses. Let `F̄` be the free group on `S̄`
(the identity sent to `1`), `N̄ = ker(F̄ -> Ḡ)`, and `π: F -> F̄`, `s ↦ s̄`.

**(RL) Relators lift:** `N̄ = π(N)`. The inclusion `⊇` always holds. `(RL)` holds, for example,
when some section-closed `S' ⊆ S` maps onto `S̄ \ {1}` and restriction is injective on `⟨S'⟩`.

## Statement

**Theorem.** Assume (RL). If `N = ⟨⟨R⟩⟩_lift` for a finite `R ⊆ N`, then `N̄ = ⟨⟨π(R)⟩⟩_lift` in `F̄`.
Consequently, if `V_{|X|}(G)` is finitely presented, so is `V_{|W|}(Ḡ)`.

**The converse fails.**
- Take Grigorchuk's group with the persistent action on `{0,1,2}^*` (`s(2) = 2`, `s|_2 = s`).
- `W = {0,1}` is invariant, and restriction gives the standard action, faithfully, so (RL) holds with
  `S' = S`.
- The standard action is lift-presented: Grigorchuk's group is contracting, so `V_2` is finitely
  presented (Nekrashevych).
- The persistent action is not lift-presented: `V_3` is not finitely presented (SWZ Example 7.2, and
  `persistent-automata-rn-group-fp-iff-group-fp`).

So lift-presentation can be lost when letters are added, and the theorem only passes it downward.

## Application: the Wächter–Weiß test input

- *Setting.* Let `R` be finite, acting off the encoding letters `W = {■0, ■1}`. Let `G_R` be the
  PSPACE-hard Wächter–Weiß automaton group of `finite-commutator-wachter-weiss-groups-are-not-fp`, and
  `C` its restriction to `W^*`, the binary check-mark automaton group.
- *Hypotheses.* Every state preserves `W`. The check-mark states with continuation `id` form a
  section-closed `S'` on which restriction is injective and onto the states of `C` (step 1b there).
- *Conclusion.* **So if `V_{|Σ|}(G_R)` is finitely presented, then `V_2(C)` is finitely presented.**
- *Two remarks.* This is weaker than asking `G_R` or `C` to be finitely presented, which Boone–Higman
  does not need: `lift-presented-automaton-groups-satisfy-boone-higman` asks only for lift-presentation.
  And `C` is a single explicit two-letter automaton, independent of `R` and of the Turing machine.

## Lesson for general BH

Lift-presentation, the finiteness condition that the automaton route to Boone–Higman actually
consumes, is inherited by invariant sub-alphabets under relator lifting, and not conversely. So:
- **Negative direction.** To show a self-similar action is not lift-presented, it suffices to find an
  invariant sub-alphabet whose restricted action is not lift-presented and whose relators lift. This
  is a second retraction test next to loop retraction.
- **Positive direction.** Adding letters is exactly where lift-presentation can fail (persistence). A
  construction of lift-presented overgroups (`automaton-groups-embed-in-lift-presented-automaton-groups`)
  must therefore enlarge the action in a way that kills relators, not merely repeat them.

DERIVATION
lift-presentation-passes-to-invariant-subalphabets-proof
