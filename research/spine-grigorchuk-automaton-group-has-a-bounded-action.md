---
rg: 2
id: spine-grigorchuk-automaton-group-has-a-bounded-action
kind: claim
title: The spine-Grigorchuk group, whose three-letter Nekrashevych group is not finitely presented, has a bounded action on four letters, so it satisfies Boone–Higman through a self-similar host
distinct_from:
  linear-activity-automata-can-have-non-fp-nekrashevych-groups: that shows the three-letter action is bad (V_3 not finitely presented); this gives a good action of the same group.
  commonly-fixed-letters-compress-to-faithful-actions: that is the general construction; this is its first application.
---

**ESTABLISHED** (lane proof below; no priority claimed). Referee a (proof gaps) PASS: `research/artifacts/gq-referee-a-commonly-fixed-letters-compress-and-spine-grigorchuk.md`.

## Statement

Let `G = ⟨a,b,c,d,ŝ_a,ŝ_b,ŝ_c,ŝ_d⟩ <= Aut({0,1,2}^*)` be the group of
`linear-activity-automata-can-have-non-fp-nekrashevych-groups` (Grigorchuk generators with trivial sections at
`2`, and `ŝ_γ = (γ, 1, ŝ_γ)`). Then `G` has a faithful action on `A^*`, `A = {0,1} × {0,1}` (four letters), by a
bounded automaton with the same eight nontrivial states. That action is contracting, so `V_4(G)` is finitely
presented (Nekrashevych FP2). `G` embeds in a finitely presented simple group, unconditionally, by the route in
the Conclusion.

## Proof

- **Compression.** Every state fixes `2`, and `σ = (·)|_2` sends `a,b,c,d` to `1` and fixes each `ŝ_γ`. So
  `p = 1`, `q = 1`, and `commonly-fixed-letters-compress-to-faithful-actions` gives a faithful action on
  `A = {0,1} × {0,1}`:
  - on letters `(y,0)` every state acts as before on `y` with its old section at `y`;
  - on letters `(y,1)`: `a,b,c,d` fix them with trivial sections; `ŝ_γ` fixes them, with section `γ` at
    `(0,1)` and `1` at `(1,1)`.
  So `ŝ_γ` has sections `γ, 1, γ, 1` at `(0,0),(1,0),(0,1),(1,1)`: its self-loop is gone.
- **Bounded and contracting.** In the new automaton the only cycle through nontrivial states is Grigorchuk's
  `b -> c -> d -> b` along `(1,0)`, and every `ŝ_γ` has only Grigorchuk sections. The subgroup `Γ = ⟨a,b,c,d⟩`
  acts on `(y,0)`-letters by Grigorchuk's recursion and trivially below `(y,1)`, so it is contracting with
  Grigorchuk's length bound `|γ|_v| <= (|γ|+1)/2` for `|v| = 1` on `(y,0)`, and with trivial sections on `(y,1)`.
  Every level-one section of every `g in G` is a product of sections of letters, all of which lie in `Γ`. So all
  sections of `g` at level `1 + k` lie in the sections of a `Γ`-element of length `<= |g|` at level `k`, which are
  in Grigorchuk's nucleus `{1,a,b,c,d}` for `k` large. Hence `G` is contracting on `A^*` with that nucleus.
- **Conclusion.** Nekrashevych's FP2 (`rover-nekrashevych-finite-presentation-criteria`) makes `V_4(G)` finitely
  presented. Boone–Higman for `G`, unconditionally: every element preserves the second coordinate of `A`, and
  the sections at `(1,1)` are trivial, so `G` embeds in `(Γ ≀ C_2) × Γ` (the `(·,0)` cones carrying `Γ`
  with the swap, the `(0,1)` cone carrying `Γ`). That group lies in Röver's group `V Γ` (two cones for
  `Γ ≀ C_2` with a `V`-swap, a third for `Γ`), which is finitely presented and simple (Röver). Alternatively,
  via the necessity half of Theorem A (`rover-nekrashevych-fp-iff-finite-lift-presentation`, not yet refereed),
  the relator kernel is a finitely generated lift ideal and `lift-presented-automaton-groups-satisfy-boone-higman`
  gives the commutator host `[V_{4m}(G),V_{4m}(G)]`.

## Remark

Boone–Higman for this `G` also follows from `G ≤ (Γ ≀ C_2) × Γ`. The point here is the method: the bad action
was repaired by compression alone, with the same states.
