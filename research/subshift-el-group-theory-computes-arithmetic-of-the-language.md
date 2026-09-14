---
rg: 2
id: subshift-el-group-theory-computes-arithmetic-of-the-language
kind: claim
title: The first-order theory of EL_3(LC(X,F_2)⋊Z) is recursively isomorphic to the theory of arithmetic with a predicate for the language of X, so for recursive languages the group is quasi-finitely axiomatizable
distinct_from:
  subshift-el-group-bi-interpretable-with-its-ring: that is the group-to-ring half, and it is established; this asks for the ring-to-arithmetic half, which needs a definable coding of finite words inside the ring.
  subshift-elementary-group-word-problem-degree: that measures one decision problem, the word problem, and puts it at the degree of the language; this measures the whole elementary theory.
  marked-subshift-elementary-group-determines-language: that recovers the language from the marked group; this asks for a first-order interpretation, which is much stronger.
artifacts:
  - research/artifacts/sk-first-order-plan-2026-09-14.md
---

**OPEN.** Let `X` be an infinite minimal subshift, `R = LC(X,F_2)⋊_T Z` and `G = EL_3(R)`. The claim is that `G` is bi-interpretable with `(N,+,·,L(X))`, with parameters. Three consequences would follow.

- `Th(G_X)` and `Th(N,+,·,L(X))` are recursively isomorphic after adjoining finitely many constants. So `Th(G_X)` is hereditarily undecidable for every `X`.
- `G_X ≡ G_Y` forces `L(X)` and `L(Y)` to satisfy the same arithmetic sentences.
- When `L(X)` is **recursive**, the predicate is arithmetically definable, so `G_X` is bi-interpretable with `N` itself. By Nies's theorem it is then quasi-finitely axiomatizable and prime: a single first-order sentence pins `G_X` down among finitely generated groups. The Sturmian subshifts with computable slope of the note's word-problem corollary are of this kind, so infinitely many pairwise non-isomorphic infinite simple Kazhdan LEF groups would be described by one sentence each.

## What is already done
`subshift-el-group-bi-interpretable-with-its-ring` reduces the claim to the same statement about the ring: it is enough that `R_X` is bi-interpretable with `(N,+,·,L(X))`.

## Attempts
- **The easy direction looks routine.** `R_X` is interpretable in `(N,+,·,L(X))` with no parameters: code `r ∈ R` by a `u`-degree bound, a window radius and a table of values on words of that length; equality and the ring operations are read off `L(X)`, which is exactly the predicate available.
- **The hard direction is a coding problem.** Needed: `(N,+,·)` and the predicate `L(X)` interpretable in `R_X` with parameters.
  - Arithmetic should come from the `Z`-direction. `C_R(u) = F_2[u^{±1}]` is definable with parameter `u`, by the same invariance computation that gives `Z(R) = F_2`.
  - The predicate is within reach once finite words are coded: for `v ∈ A^m` the cylinder idempotent `c_v = ∏_{t<m} u^{-t} e_{v_t} u^t` satisfies `v ∈ L(X) ⟺ c_v ≠ 0`, so `L(X)` is definable as soon as the map `v ↦ c_v` is. This is the standard Gödel-coding step and it is where the work sits: a first-order definable coding of finite sequences inside `R`.
  - The Boolean side cannot supply arithmetic on its own: `LC(X,F_2)` is a countable atomless Boolean ring, whose theory is decidable.
- **Two imports, both UNVERIFIED at source.**
  - Undecidability of the first-order theory of `F_q[t]`, or of the Laurent ring `F_q[t^{±1}]`. Candidate sources: Denef, *The Diophantine problem for polynomial rings of positive characteristic* (1979); Shlapentokh on rings of `S`-integers of function fields over finite fields, of which `F_q[t^{±1}]` is one. Bound of the check: two web searches, which returned the function-**field** results of Pheidas, Videla, Shlapentokh and Eisenträger rather than the polynomial-**ring** statement. No source was opened.
  - Nies, *Describing groups*, Bull. Symbolic Logic 13 (2007): a finitely generated group bi-interpretable with `N` is quasi-finitely axiomatizable and prime. To check: whether his hypothesis permits parameters, which is what the route above would supply.
- **Firewall.** Everything here needs `X` infinite and minimal, so that `T` is aperiodic and `Z(R) = F_2`. For periodic `X` the interpretation of the ring in the group already fails.
