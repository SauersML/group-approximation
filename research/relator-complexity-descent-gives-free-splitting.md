---
rg: 2
id: relator-complexity-descent-gives-free-splitting
kind: claim
title: If some well-founded complexity on reduced words never increases under sections and strictly drops at every section of every nontrivial relator, then every relator splits freely and V_d(G) is finitely presented
distinct_from:
  rover-nekrashevych-fp-iff-finite-lift-presentation: that characterizes finite presentation of V_d(G) by lift ideals and records N = K_∞ as the case where the recursion alone suffices; this is a checkable criterion for N = K_∞.
  lift-presented-automaton-groups-satisfy-boone-higman: that consumes a lift-presented action; this certifies one without contraction or finite presentation.
---

**ESTABLISHED** (lane proof below, elementary; the consequence for `V_d(G)` uses consequence 2 of Theorem A of
`rover-nekrashevych-fp-iff-finite-lift-presentation`, not yet refereed; no priority claimed).

## Statement

Let `G = ⟨S⟩ <= Aut(X^*)`, `S` finite and closed under sections and inverses, `F = F(S)`, `N = ker(F -> G)`,
`K_∞ = ⟨⟨∅⟩⟩_lift`. Let `c` map reduced words of `F` to a well-ordered set. Suppose that for every nontrivial
`w in N` (reduced) and every `x in X`, the reduced section `red(w|_x)` satisfies `c(red(w|_x)) < c(w)`. Then
`N = K_∞`: every relator becomes freely trivial after finitely many splittings. Consequently `V_d(G)` is
finitely presented by the recursion relations alone, and `G` embeds in a finitely presented simple group
(`lift-presented-automaton-groups-satisfy-boone-higman`).

## How it is used

Typically `c` counts letters by degree (activity class), lexicographically from the top, so that `c` never
increases under sections and stays equal only on words in which every letter follows its own cycle edge at the
point it receives. One then shows that no nontrivial relator is such a word. First application:
`linear-activity-odometer-automaton-has-fp-nekrashevych-group`.

## Proof

Well-founded induction on `c(w)` over reduced `w in N`. The empty word lies in `K_∞`. Let `w in N` be
nontrivial. It acts trivially, so it has trivial root permutation, and each `w|_x` lies in `N` (sections of
relators are relators); `red(w|_x)` has smaller complexity, so it lies in `K_∞` by induction, and so does `w|_x`
(same element of `F`). `K_∞` is a lift ideal, so `w in K_∞`. Hence `N ⊆ K_∞ ⊆ N`. ∎
