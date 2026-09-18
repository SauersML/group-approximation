---
rg: 2
id: spinal-extensions-of-lift-presented-groups-satisfy-boone-higman
kind: claim
title: Adding to a lift-presented automaton new states that loop along a commonly fixed letter and have base sections elsewhere gives a group with a lift-presented action, hence a Boone–Higman group
distinct_from:
  spine-grigorchuk-automaton-group-has-a-bounded-action: that is one instance (Grigorchuk base, spine copies); this is the general statement for any lift-presented base and any spinal states.
  finitary-extensions-preserve-lift-presentability: that adds states with base sections at a fixed depth; here the new states also loop along a letter, which compression removes first.
---

**ESTABLISHED** (lane proof below; not yet refereed; no priority claimed).

## Statement

Let `S = S_0 ⊔ S_1 <= Aut(X^*)` be finite and closed under sections and inverses, with `S_0` closed under
sections and inverses. Suppose there is a letter `x` with
1. `s(x) = x` for every `s in S`;
2. `s|_x = 1` for every `s in S_0`;
3. `s|_y in S_0 ∪ {1}` for every `s in S_1` and every `y ≠ x`;
4. the action of `G_0 = ⟨S_0⟩` on `X^*` is lift-presented (equivalently `V_{|X|}(G_0)` is finitely presented;
   e.g. `G_0` contracting or finitely presented).

Then the compressed action of `G = ⟨S⟩` at `x` (`commonly-fixed-letters-compress-to-faithful-actions`) is
lift-presented. So `G` has a finitely presented Rover–Nekrashevych group and embeds in a finitely presented
simple group, although its original action may not be lift-presented
(`linear-activity-automata-can-have-non-fp-nekrashevych-groups` is an instance).

## Proof

- **Compression.** By 1, compress at `x`: `σ(s) = s|_x`, alphabet `A = (X∖{x}) × {0,…,p+q-1}`, and `s` has
  section `σ^c(s)|_y` at `(y,c)`. By 2, `σ(S_0) = {1}`. For `s in S` and `c >= 0`, `σ^c(s)` lies in `S`; its
  sections at `y ≠ x` lie in `S_0 ∪ {1}`, by 3 if it is in `S_1` and by closure of `S_0` otherwise. So in the
  compressed action every section of every state lies in `S_0 ∪ {1}`.
- **The base stays lift-presented.** For `s in S_0`, the compressed recursion is the old one on letters `(y,0)`
  and trivial on letters `(y,c)`, `c >= 1`. A word `w in F(S_0)` has trivial compressed root permutation iff it
  has trivial old root permutation (`x` is fixed anyway). Its compressed sections are the old `w|_y` and empty
  words, while its old section at `x` is `σ(w)`, the empty word. So the compressed and old lift conditions
  coincide on `F(S_0)`, the lift ideals of `F(S_0)` are the same, and `G_0`'s compressed action is
  lift-presented with the same relators.
- **Conclusion.** `finitary-extensions-preserve-lift-presentability` with `k = 1` makes the compressed action of
  `G` lift-presented. Then `lift-presented-automaton-groups-satisfy-boone-higman` applies. ∎

## Where the general case stands

By `finitary-extensions-preserve-lift-presentability`, lift-presentability of an automaton reduces to its
nontrivial strongly connected components over lift-presented bases. This node settles a component that is a
loop along a letter fixed by everything, over a base with trivial sections there. The sharpest remaining test is
a loop whose letter the base moves, e.g. the linear-activity automaton `a = σ(1, a)`, `b = (a, b)` over
`{0,1}`: the base `⟨a⟩ ≅ Z` is lift-presented, but `a` moves the loop letter of `b`, so compression does not
apply. Whether `V_2(⟨a,b⟩)` is finitely presented is open here.
