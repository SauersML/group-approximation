---
rg: 2
id: effective-minimal-free-subshifts-via-coherent-greedy-tower
kind: route
title: The coherent greedy margin covering tower is a computable margin covering tower whenever it never stalls, so (G_geo) gives (M2)
target: decidable-fp-groups-have-effective-minimal-free-subshifts
requires:
  - covering-towers-iff-effective-minimal-free-subshifts
  - norm-greedy-towers-stall-at-symmetric-dead-end-spots
  - translation-coherent-greedy-margin-towers-never-stall
---

**Route. OPEN.** Two premises are ESTABLISHED:
- `covering-towers-iff-effective-minimal-free-subshifts`;
- Theorem 3.1 of `norm-greedy-towers-stall-at-symmetric-dead-end-spots`.

The third, (G_geo) `translation-coherent-greedy-margin-towers-never-stall`,
is OPEN. This route is an alternative to
`effective-minimal-free-subshifts-via-greedy-maximal-tower`, whose recursion
can stall at Cayley dead ends.

**Argument.** Let `Λ` be infinite, finitely presented, with solvable word
problem. Take the generating set and data `(A, R)` from (G_geo), and `R_n`,
`L_n`, `m_n = n` as there.

1. *Computability.* `F^geo_n(R)` is decidable uniformly in the finite data,
   by Theorem 3.1. By (G_geo) the search over admissible `R` halts at every
   level. So `n ↦ (R_n, L_n)` is computable, and every `L_n` is finite and
   nonempty.
2. *Radii.* `R_{n+1} ≥ R_n + 2(n+1)`, so `R_n ≥ n(n+1)`. Hence
   `0 ≤ m_n ≤ R_n ≤ R_{n+1}`, `m_n → ∞` and `R_n − m_n → ∞`.
3. *Tower conditions.*
   - For `q ∈ L_{n+1} = F^geo_n(R_{n+1})`, clauses (C) and (K) are literally
     the tower conditions (C) and (K) at level `n+1`.
   - Clause (A_geo) with radius `R_{n+1}` implies clause (A) with the same
     function `R` (Theorem 3.1). That is tower condition (A) at level `n+1`.
   - At level `0`, (A) is vacuous.
4. So `(A, R_n, m_n, L_n)` is a computable margin covering tower. Direction
   2 ⇒ 1 of `covering-towers-iff-effective-minimal-free-subshifts` gives a
   nonempty effectively closed subshift on which `Λ` acts minimally and
   freely. That is (M2).
