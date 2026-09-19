---
rg: 2
id: spine-mover-automata-over-fp-bases-are-lift-presented
kind: claim
title: The spine-plus-odometer-mover automaton over a finitely presented self-similar group is lift-presented, so the recurrent-mover test case reduces to a finitely presented self-similar overgroup of its lamp group
distinct_from:
  spine-and-odometer-mover-generate-a-2-adic-lamplighter: that decomposes the Grigorchuk test case and isolates the 2-adic lamplighter; this proves the same automaton shape is lift-presented whenever the lamp group is finitely presented, and so reduces the test case to an existing open node.
  polynomial-automata-reduce-to-cycling-relators: that needs every state to have at most one section in its component; here the base group is arbitrary (any activity), and its relators are absorbed through its own lift ideal.
  decidable-fg-self-similar-groups-embed-in-fp-self-similar: that is the self-similar Higman question; for the Grigorchuk group it is now exactly what the recurrent-mover test case needs.
---

**ESTABLISHED** (lane proof below, elementary; uses Theorem A of
`rover-nekrashevych-fp-iff-finite-lift-presentation`; not yet refereed; no priority claimed).

## The automaton `M(P)`

Let `P = ⟨S_P⟩ <= Aut(Y^*)` be self-similar with `S_P` finite and closed under sections and inverses. On
`X = Y ⊔ {2,3}` define:
- **base:** each `s in S_P` acts on `Y`-letters as before and fixes `2, 3` with trivial section;
- **spine:** for `p in S_P`, `ŝ_p` acts on `y in Y` as `p` (output `p(y)`, section `p|_y`), keeps itself on `2`,
  and dies on `3`; so `ŝ_p` applies `p` after a maximal run `2^k` that is followed by a `Y`-letter;
- **mover:** `n = (2 3)(1_Y, 1, n)`: it fixes `Y` with trivial sections, and on `{2,3}`-prefixes it is the odometer
  (`3` is the digit 1, loop at `3`), with `n^{-1}` looping at `2`.
`p ↦ ŝ_p` extends to an injective homomorphism `P -> Aut(X^*)`. With `P` = Grigorchuk's group (or `⟨Γ, (Γ,1)⟩`
for rigid-copy lamps), `M(P)` is the four-letter test case of
`spine-and-odometer-mover-generate-a-2-adic-lamplighter`.

## Statement

**Theorem.** If `P` is finitely presented, the action of `M(P)` is lift-presented. So `V_{|X|}(⟨M(P)⟩)` is
finitely presented, and `⟨M(P)⟩` embeds in a finitely presented simple group.

**Corollary.** Let `Γ <= Aut(Y^*)` be finitely generated and self-similar. If `Γ` lies in a finitely presented
self-similar group `P <= Aut(Y^*)` (the same tree action), then `⟨M(Γ)⟩ <= ⟨M(P)⟩` is LP-embeddable and
Boone–Higman. For the Grigorchuk test case, rigid copies included, use `P ≀ C_2`, which is again finitely
presented and self-similar. So that test case is settled by any finitely presented self-similar overgroup of
the Grigorchuk group on the binary tree, an instance of `decidable-fg-self-similar-groups-embed-in-fp-self-similar`.

## Proof

Let `F = F(S)` for the state set `S = S_P ∪ {ŝ_p^{±}} ∪ {n^{±}}`, and `N` its relator kernel.
- `P` finitely presented gives a finite `R_P` with `N ∩ F(S_P) = ⟨⟨R_P⟩⟩_lift` in `F(S_P)`
  (Theorem A, consequence 1).
- Let `r_1, …, r_m` be a finite presentation of `P` on `S_P`.
- Put `R = R_P ∪ {r_i(ŝ)}` and `M = ⟨⟨R⟩⟩_lift` in `F`.

**Base relators.** `M ∩ F(S_P)` is a lift ideal of `F(S_P)` for `P`'s own recursion (sections of base words at
`2, 3` are empty), and it contains `R_P`, so it contains `N ∩ F(S_P)`.

**Spine relators.** A word in the letters `ŝ_p^{±}` is a relator iff the corresponding word in `S_P` is a relator
of `P` (injectivity of `p ↦ ŝ_p`). So it lies in `⟨⟨r_i(ŝ)⟩⟩ ⊆ M`.

**Complexity.** For a reduced word `w` let `β(w)` count the non-base letters (`ŝ^{±}`, `n^{±}`) and `α(w)` the
base letters, ordered lexicographically. Section rules:
- a base letter keeps a base letter at a `Y`-point and dies at `2, 3`, passing the point on;
- `ŝ` keeps itself at `2` (outputs `2`), becomes a base letter at a `Y`-point, and dies at `3`;
- `n` keeps itself at `3` (outputs `2`) and dies elsewhere;
- `n^{-1}` keeps itself at `2` (outputs `3`) and dies elsewhere.

So `c(red(w|_x)) <= c(w)`. Suppose equality holds.
- Every non-base letter receives its loop letter, and none cancel.
- Non-base letters output `2` or `3`, so a base letter directly to the left of a non-base letter would die.
  Hence all base letters lie to the right of all non-base letters.
- The rightmost non-base letter would then receive a `Y`-point from a base letter, so there are none.

So `w` is all-base, or all non-base with every letter on its loop. In the second case:
- `n^{-1}` must be leftmost (only `n` accepts `3`, and `n n^{-1}` is not reduced);
- `n` must be rightmost (only `n^{-1}` outputs `3`);
- so `w in {v, n^{-1}v, v n, n^{-1} v n}` with `v` a spine word, and `w|_x = w`.

Among these, the relators are the spine relators `v` and their conjugates `n^{-1}vn`. The words `n^{-1}v` and
`v n` move the ray `2^ω` or `3^ω`, so they are not relators.

**Induction** on `c` over reduced relators `w`:
- if `β(w) = 0`, `w in M` by the base case;
- if `w` is special at some `x`, then it is a spine relator or its conjugate, and `w in M`;
- otherwise every section is a relator of smaller complexity, hence in `M`, and one lift step gives `w in M`.

So `N = M`. ∎

## Remarks

- The theorem does not need `P` to have subexponential activity. The base is absorbed through its own lift
  ideal, and descent is used only on the spine and mover letters.
- Whether `M(P)` is lift-presented only if `P` is finitely presented is not settled here. A retraction as in
  `loop-retraction-forces-fp-eventual-section-groups` would need a letter fixed by every state, and `n`
  moves `2`.
