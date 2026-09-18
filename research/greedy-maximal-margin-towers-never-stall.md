---
rg: 2
id: greedy-maximal-margin-towers-never-stall
kind: claim
title: Over every infinite finitely presented group with solvable word problem, for some alphabet and computable freeness radius the greedy maximal margin covering tower never stalls
distinct_from:
  nonempty-tower-classes-yield-computable-towers: that asks for a computable path in an arbitrary nonempty tower class and is a computability-theoretic basis statement; this fixes one canonical decidable recursion (take at each level ALL admissible patches) and asks only that a finite search halt at every level, so no path has to be selected.
  free-minimal-subshifts-with-computable-moduli-exist: that is (N), nonemptiness of some tower class; this implies (N) and (M2), and is a Pi02 statement about finite patch sets for fixed data.
  decidable-groups-have-overlap-recurrent-aperiodic-points: that is the one-patch case L_n = {P_n}, where a choice of P_{n+1} extending P_n must be made; here L_n is the maximal admissible family and nothing is chosen.
  covering-towers-iff-effective-minimal-free-subshifts: that is the ESTABLISHED equivalence (M2) iff a computable margin covering tower exists; this is an OPEN existence statement for one explicit tower.
---

**OPEN.** Statement (G).

**Setting.** Conventions of `covering-towers-iff-effective-minimal-free-subshifts`:
`|g|` is word length, `d(x,z) = |x z^{-1}|`, and the window is
`w_R(q,h)(μ) = q(μh)`.

**Data.** A finite alphabet `A` and a computable `R : G∖{1} → N`. Put
`m_n = n`.

**Greedy recursion.** Start with `R_0 = 0` and `L_0 = A^{B(0)}`, the single
letters. Given the finite set `L_n` of patterns `B(R_n) → A` and a radius
`R ≥ R_n + 2(n+1)`, let `F_n(R)` be the set of `q : B(R) → A` such that:
- **(C)** for every `g ∈ B(R − m_{n+1})` there is `h` with `d(g,h) ≤ R_n − m_n`,
  `|h| ≤ R − R_n` and `w_{R_n}(q,h) ∈ L_n`;
- **(K)** for every `p ∈ L_n` there is `c ∈ B(R − R_n)` with `w_{R_n}(q,c) = p`;
- **(A)** for every `s ≠ 1` and every `c` with `|c| ≤ R − R(s) − |s|`, some
  `μ ∈ B(R(s))` has `q(μc) ≠ q(μsc)`.

`F_n(R)` is a decidable finite set, uniformly in `n`, `R` and `L_n`, because
balls are computable under a solvable word problem. Let `R_{n+1}` be the least
admissible `R` with `F_n(R) ≠ ∅`, and set `L_{n+1} = F_n(R_{n+1})`. The
recursion **stalls at level `n`** if `F_n(R) = ∅` for every `R`.

**Statement (G).** Let `Λ` be an infinite finitely presented group with
solvable word problem. Then there are data `(A, R)` for which the greedy
recursion never stalls.

**Consequence (complete, route `effective-minimal-free-subshifts-via-greedy-maximal-tower`).**
(G) for `Λ` implies (M2) for `Λ`, and therefore (N).

## Attempts

None yet. The obstruction analysis is in Attempt 5 of
`decidable-fp-groups-have-effective-minimal-free-subshifts`.
