---
rg: 2
id: relative-finite-discrimination-forces-solvable-word-problem
kind: claim
title: If every nontrivial element of a finitely generated subgroup K normally generates, inside a recursively presented group G, a subgroup meeting a fixed r.e. set of nontrivial elements, then K has solvable word problem
distinct_from:
  limits-of-isolated-groups-basic-closure: that records the structure of the limits of isolated groups; this is a decidability lemma used to test proposed counterexamples to Cornulier--Guyot--Pitsch Questions 1 and 3.
  simple-envelope-forces-solvable-word-problem: that is Kuznetsov's theorem for subgroups of recursively presented simple groups; this relativizes Cornulier--Guyot--Pitsch Theorem 3.4 to a subgroup and a discriminating set in the ambient group, and derives the no-fixed-subgroup corollary.
---

**ESTABLISHED** (lane proof below, elementary, not reviewed; no priority claimed: it is the
proof of Cornulier--Guyot--Pitsch Theorem 3.4, arXiv:math/0511714v2 p. 10, run relative to a
subgroup).

**Statement.** Let `G = ⟨X | R⟩` with `X` finite and `R` recursively enumerable, and let
`K = ⟨k_1, …, k_n⟩ ≤ G`, each `k_j` given as a word in `X`. Suppose there is a recursively
enumerable set `F` of words, each nontrivial in `G`, such that `⟨⟨k⟩⟩_G ∩ F ≠ ∅` for every
`k ∈ K − {1}`. Then `K` has solvable word problem.

**Corollary (no fixed-subgroup transfer).** Let `G` be finitely presented (or recursively
presented) and let `K ≤ G` be finitely generated with unsolvable word problem. Then for every
finite `F ⊂ G − {1}` there is `k ∈ K − {1}` with `⟨⟨k⟩⟩_G ∩ F = ∅`. So the finitely
presented quotient `G/⟨⟨k⟩⟩` lies in the basic neighbourhood "all `f ∈ F` nontrivial" of
`G`, and `K` does not embed in it through the quotient map. No finitely generated subgroup
with unsolvable word problem survives in all nearby finitely presented quotients of `G`.

**Proof.** Given a word `u` in the `k_j`, rewrite it as a word `ū` in `X`. Run two searches
in parallel.
- (a) Enumerate the consequences of `R`, looking for `ū = 1`.
- (b) Enumerate `f ∈ F`, finite products `Π_i g_i ū^{±1} g_i^{-1}` with `g_i` words in `X`,
  and consequences of `R`, looking for `Π_i g_i ū^{±1} g_i^{-1} = f`.

If `ū = 1` in `G`, then (a) halts, and (b) never does, because `⟨⟨ū⟩⟩ = 1` while every
`f ∈ F` is nontrivial. If `ū ≠ 1`, then (a) never halts, and by hypothesis some `f ∈ F`
lies in `⟨⟨ū⟩⟩`, so (b) halts. Exactly one search halts, and it answers the question.

For the corollary, a finite `F` is recursively enumerable, so the conclusion "unsolvable" forces
the hypothesis to fail for some `k ∈ K − {1}`. `G/⟨⟨k⟩⟩` is finitely presented when `G` is,
and it keeps every `f ∈ F` nontrivial because `⟨⟨k⟩⟩ ∩ F = ∅`; `k` itself dies, so the
quotient map is not injective on `K`.

**Use.** CGP's own Corollary 3.5 (isolated groups have solvable word problem) is the case
`K = G` with `F` a finite discriminating set. The corollary above shows that a negative answer
to `every-fg-solvable-group-is-a-limit-of-isolated-groups` (CGP Question 3) cannot be obtained
by the naive route their remark suggests, namely a finitely presented solvable group whose
unsolvable word problem lives in one fixed subgroup that embeds in every nearby quotient.
Unsolvability in the nearby quotients, if it is used at all, must be carried by subgroups that
vary with the quotient.
