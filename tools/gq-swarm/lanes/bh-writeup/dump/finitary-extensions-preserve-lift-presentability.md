---
rg: 2
id: finitary-extensions-preserve-lift-presentability
kind: claim
title: Adding states whose sections at some fixed depth lie in a lift-presented sub-automaton keeps the relator kernel a finitely generated lift ideal, with the same relators
distinct_from:
  lift-presented-automaton-groups-satisfy-boone-higman: that turns one lift-presented action into a finitely presented simple host; this enlarges the class of lift-presented actions.
  lift-presentability-is-invariant-under-level-regrouping: that compares level-1 and level-m lift conditions for one automaton; this adds states to an automaton, and uses that node to allow any depth.
---

**ESTABLISHED** (lane proof below, elementary; relies on Theorem A of
`rover-nekrashevych-fp-iff-finite-lift-presentation` only through
`lift-presentability-is-invariant-under-level-regrouping` for depth `k > 1`; not yet refereed; no priority
claimed).

## Statement

Let `S <= Aut(X^*)` be finite and closed under sections and inverses, and let `S_0 ⊆ S` be closed under sections
and inverses, with `G_0 = ⟨S_0⟩`, `F_0 = F(S_0) <= F = F(S)`, and relator kernels `N_0 = N ∩ F_0`, `N`. Suppose
`N_0 = ⟨⟨R_0⟩⟩_lift` in `F_0` for a finite `R_0`, and that for some `k >= 1` every section of every state of `S`
at level `k` lies in `S_0 ∪ {1}`. Then `N = ⟨⟨R_0⟩⟩_lift` in `F` for level `k = 1`, and `N` is a finitely
generated lift ideal for every `k`. So `V_d(⟨S⟩)` is finitely presented whenever `V_d(G_0)` is, and `⟨S⟩` embeds
in a finitely presented simple group (`lift-presented-automaton-groups-satisfy-boone-higman`).

## Proof

- **`k = 1`.** `M = ⟨⟨R_0⟩⟩_lift` computed in `F` meets `F_0` in a lift ideal of `F_0` (normal in `F_0`, and
  lift-closed there because sections of words in `F_0` are words in `F_0`) containing `R_0`, so
  `N_0 ⊆ M`. Let `w in N`. It has trivial root permutation, and each section `w|_y` is a product of level-1
  sections of letters, hence a word in `F_0`, and lies in `N` (sections of relators are relators). So
  `w|_y in N ∩ F_0 = N_0 ⊆ M`, and one lift step gives `w in M`. Thus `N = M`.
- **`k > 1`.** Pass to the level-`k` action. `G_0`'s level-`k` action has relator kernel `N_0`, a finitely
  generated level-`k` lift ideal by `lift-presentability-is-invariant-under-level-regrouping`; the `k = 1`
  argument, read at level `k`, makes `N` a finitely generated level-`k` lift ideal; transfer back by the same
  node. ∎

## Consequences

- Transient states (nontrivial states on no cycle of the section graph) have all their sections at depth
  `k` = (number of transient states) + 1 in the sub-automaton `S_0` spanned by the nontrivial strongly connected
  components and everything below them. So `⟨S⟩` is lift-presented as soon as `⟨S_0⟩` is: lift-presentability
  reduces to automata in which every nontrivial state lies on a cycle.
- With run compression: `spinal-extensions-of-lift-presented-groups-satisfy-boone-higman`.
