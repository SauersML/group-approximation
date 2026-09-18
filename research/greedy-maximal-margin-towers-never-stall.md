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

The general obstruction analysis is in Attempt 5 of
`decidable-fp-groups-have-effective-minimal-free-subshifts`.

**Attempt 1 (swarm-0917-w9, host-geometry; a stall certificate and a repair,
status unchanged).** Recorded in
`norm-greedy-towers-stall-at-symmetric-dead-end-spots` (ESTABLISHED).

- *Stall certificate (Theorem 1 there).* Let `n ≥ 1` and `p ∈ L_n`. Suppose:
  - `p` is `s`-symmetric on the read set `Q_y(s) ⊆ B(R_n)` of a test
    `(s, y)`;
  - `y` is a right dead end of depth `k`;
  - `|y| + R(s) + |s| ≤ R_n + min(k, 2n+2)`.

  Then every placement of `p` required by (K) moves the spot to `yc` with
  `|yc| ≤ R − R(s) − |s|`, where (A) tests it and fails. So `F_n(R) = ∅` for
  all `R`.
- *Where the certificate can live.* Such a spot is invisible to level `n − 1`
  exactly when `|y| > R_n − R(s) − |s|`, so it needs `k ≥ 1`.
  - Without Cayley dead ends the certificate is vacuous.
  - With deep two-sided dead ends it is live. Examples: `y` and `y^{-1}` both
    deep, which makes `Q_y(s) ⊆ B(|y|)`.
- *The class that dies.* Every norm-tested greedy recursion dies on a level
  that contains such a pattern. The named invariant is dead-end depth of the
  generating set. The failing step is (K) followed by (A) at `yc`.
- *Not proved: a refutation of (G).* That would need, for **all** data
  `(A, R)`, some level whose maximal family `L_n` contains a certificate.
  Building one by modifying a `p_0 ∈ L_n` on `Q_y(s)` can break the earlier
  clauses in two ways.
  - It can break (C) windows of level `n − 1`.
  - It can break conjugate tests `(x s x^{-1}, x y)` that read inside
    `Q_y(s)`. These are tested at level `n − 1` whenever
    `R(xsx^{-1}) + |xsx^{-1}|` is small.

  At level `1` the question is a finite constraint problem for fixed data.
  It has not been run.
- *Repair.* Test every `c` whose read set lies in the ball (A_geo). Tested
  positions then translate with placed copies (Theorem 3 there), so no member
  of any level can kill itself. This is (G_geo),
  `translation-coherent-greedy-margin-towers-never-stall`. It has the
  complete route `effective-minimal-free-subshifts-via-coherent-greedy-tower`
  to (M2). Its only remaining failure mode is straddling tests against (K).
