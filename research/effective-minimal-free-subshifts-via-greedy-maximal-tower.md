---
rg: 2
id: effective-minimal-free-subshifts-via-greedy-maximal-tower
kind: route
title: The greedy maximal margin covering tower is computable whenever it never stalls, so (G) gives (M2) with no path selection
target: decidable-fp-groups-have-effective-minimal-free-subshifts
requires:
  - covering-towers-iff-effective-minimal-free-subshifts
  - greedy-maximal-margin-towers-never-stall
---

**Route. OPEN.** One premise is ESTABLISHED
(`covering-towers-iff-effective-minimal-free-subshifts`). The other is OPEN:
(G), `greedy-maximal-margin-towers-never-stall`.

**Argument.** Let `Λ` be infinite, finitely presented, with solvable word problem.
Let `(A, R)` be data from (G), with `R_n`, `L_n` and `m_n = n` as in (G).

1. *Computability.* `L_0 = A` is given. By (G), for each `n` the search over
   `R = R_n + 2(n+1), R_n + 2(n+1) + 1, …` for `F_n(R) ≠ ∅` halts. Each test is
   decidable, uniformly in the finite data `L_n`. So `n ↦ (R_n, L_n)` is
   computable and every `L_n` is a finite nonempty set.
2. *Radii.* `R_{n+1} ≥ R_n + 2(n+1)`, so `R_n ≥ n(n+1)`. Hence
   `0 ≤ m_n = n ≤ R_n ≤ R_{n+1}`, `m_n → ∞` and `R_n − m_n ≥ n^2 → ∞`.
3. *Tower conditions.*
   - For `q ∈ L_{n+1} = F_n(R_{n+1})`, clauses (C) and (K) of `F_n` are
     literally conditions (C) and (K) of the margin covering tower at level
     `n+1`.
   - Clause (A) of `F_n`, with the same fixed `R`, is condition (A) at level
     `n+1`.
   - At level 0, condition (A) is vacuous, because `|c| ≤ 0 − R(s) − |s| < 0`
     has no solution.
4. So `(A, R_n, m_n, L_n)` is a computable margin covering tower. Direction
   2 ⇒ 1 of `covering-towers-iff-effective-minimal-free-subshifts` then gives a
   nonempty, effectively closed subshift on which `Λ` acts minimally and freely.
   That is (M2).

**How it can fail.** (G) can fail while (M2) holds. The implication is only
one way. Every `p ∈ L_n` has to occur in each `q ∈ L_{n+1}`, and it has to sit
inside a margin-covered context. So a single member of `L_n` that has no
`L_n`-covered extension stalls the recursion forever. Extendability of a patch to all radii is
only a co-r.e. property, so no decidable level-by-level pruning of dead ends is
known. See Attempt 5 of the target.
