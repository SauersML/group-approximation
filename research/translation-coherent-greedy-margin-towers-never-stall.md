---
rg: 2
id: translation-coherent-greedy-margin-towers-never-stall
kind: claim
title: Over every infinite finitely presented group with solvable word problem, for some alphabet and computable freeness radius the greedy maximal margin covering tower with read-set asymmetry tests never stalls
distinct_from:
  greedy-maximal-margin-towers-never-stall: that is (G), whose asymmetry clause tests positions by norm, |c| ≤ R − R(s) − |s|; this is (G_geo), which tests every position whose read set lies in the ball. That makes tested positions right-translation invariant and excludes the dead-end stall of norm-greedy-towers-stall-at-symmetric-dead-end-spots. Neither statement is known to imply the other, since the two recursions produce different families L_n.
  norm-greedy-towers-stall-at-symmetric-dead-end-spots: that ESTABLISHED claim gives a stall certificate for (G) and the coherence lemma for this recursion; this is the OPEN non-stalling statement for the coherent recursion.
  nonempty-tower-classes-yield-computable-towers: that asks for a computable path through an arbitrary nonempty tower class; this is one canonical decidable recursion, so no path has to be chosen.
---

**OPEN.** Statement (G_geo).

**Setting.** As in `greedy-maximal-margin-towers-never-stall`: `|g|` is word
length, `d(x,z) = |x z^{-1}|`, and `w_R(q,h)(μ) = q(μh)`. For `s ≠ 1` put
`Q_c(s) = B(R(s))c ∪ B(R(s))sc`.

**Data.** A finite alphabet `A`, a computable `R : Λ∖{1} → N`, and `m_n = n`.

**Coherent greedy recursion.** Start with `R_0 = 0` and `L_0 = A^{B(0)}`.
Given `L_n` and `R ≥ R_n + 2(n+1)`, let `F^geo_n(R)` be the set of
`q : B(R) → A` satisfying:
- **(C)** for every `g ∈ B(R − m_{n+1})` there is `h` with
  `d(g,h) ≤ R_n − m_n`, `|h| ≤ R − R_n` and `w_{R_n}(q,h) ∈ L_n`;
- **(K)** for every `p ∈ L_n` there is `c ∈ B(R − R_n)` with
  `w_{R_n}(q,c) = p`;
- **(A_geo)** for every `s ≠ 1` and every `c` with `Q_c(s) ⊆ B(R)`, some
  `μ ∈ B(R(s))` has `q(μc) ≠ q(μsc)`.

Let `R_{n+1}` be the least admissible `R` with `F^geo_n(R) ≠ ∅`, and set
`L_{n+1} = F^geo_n(R_{n+1})`. By Theorem 3.1 of
`norm-greedy-towers-stall-at-symmetric-dead-end-spots`, each
`F^geo_n(R)` is decidable, uniformly in `n`, `R` and `L_n`.

**Statement (G_geo).** Let `Λ` be an infinite finitely presented group with
solvable word problem. Then there are a finite generating set and data
`(A, R)` for which the coherent greedy recursion never stalls.

**Consequence.** (G_geo) implies (M2) for `Λ`. The route is
`effective-minimal-free-subshifts-via-coherent-greedy-tower`, complete given
(G_geo).

**What is known.**
- *Self-killing patterns cannot occur.* A placed copy of a member of `L_n`
  passes every test that reads only its own values
  (`norm-greedy-towers-stall-at-symmetric-dead-end-spots`,
  Theorem 3.2). In particular, the dead-end stall of Theorem 1 there cannot
  happen.
- *Dead ends do not obstruct the positions in (C).* An admissible window
  centre always exists. Let `|g| ≤ R − n − 1`, write `g = a_1 ⋯ a_L`
  geodesically, and put `j = max(0, L − R + R_n)`. Then `h = a_{j+1} ⋯ a_L`
  has `|h| = L − j ≤ R − R_n` and `d(g,h) ≤ j ≤ R_n − n − 1`. Whether the
  window at such an `h` can be made a member of `L_n` is part of the
  remaining failure below.
- *The remaining failure.* A stall at level `n` means that, for every `R`, no
  `q` can simultaneously place every member of `L_n` (K), cover the ball by
  `L_n`-windows (C), and pass every **straddling** test, meaning a test
  whose read set `Q_c(s)` lies in no single placed window.

## Attempts

None yet.
