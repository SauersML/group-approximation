---
rg: 2
id: unique-games-entangled-value-approximable-by-sdp
kind: claim
title: The entangled value of a unique game is within a factor 6 in the deficit of its SDP value, so the entangled UG gap is decidable (Kempe--Regev--Toner)
distinct_from:
  perfect-commuting-unique-game-is-classically-satisfiable: that is the exact zero-deficit rigidity (a perfect commuting strategy is a classical labeling); this is the quantitative near-perfect statement, where an SDP value 1-eps only yields an entangled strategy of value 1-6eps and no classical labeling at all.
  unique-games-gap-admits-polynomial-time-algorithm: that is the open classical refutation of UGC; this is the proved algorithm for the entangled value, which refutes only the entangled variant of UGC.
artifacts:
  - research/artifacts/unique-games-entangled-value-approximable-by-sdp-citation-2026-09-17.md
---

**OPEN.** A drafted proof is recorded as an attempt (see Attempts); it is not established because referees refuted the result as written. For a two-prover one-round game `G` write
`omega*(G)` for its entangled value, the limit over the local dimension `d` of
the best value of a strategy with a shared pure state in `C^d (x) C^d` and
projective measurements. Write `omega_sdp1(G)` for the value of the
Kempe--Regev--Toner semidefinite program SDP 1: real vectors `u^s_a`, `v^t_b`,
`z`, with `|z| = 1`, `sum_a u^s_a = sum_b v^t_b = z`, orthogonality of distinct
answers to one question, and `<u^s_a, v^t_b> >= 0`.

1. **Relaxation.** For every game, `omega*(G) <= omega_sdp1(G)` (KRT Lemma 3.2).
   The same proof gives `omega_qc(G) <= omega_sdp1(G)` for commuting-operator
   strategies (see the route).
2. **Rounding.** For a unique game, `omega_sdp1(G) = 1 - eps` implies
   `omega*(G) >= 1 - 6 eps` (KRT Theorem 4.5). The rounding uses copies of a
   maximally entangled state and shared randomness.
3. **Algorithm.** There is an efficient algorithm that, given a unique game of
   entangled value `1 - eps`, outputs `eps'` with `eps/6 <= eps' <= eps`
   (KRT Theorem 1.3). Hence whenever `6 eps + delta < 1` it separates entangled
   value `>= 1 - eps` from entangled value `<= delta`.

Credit is entirely theirs; nothing here reproves the rounding. This is the
operator-algebraic input to `entanglement-sound-soundness-cannot-prove-ugc`.

## Attempts

- 2026-09-17 `swarm-0917` (ugc-pull-1): candidate citation import, held OPEN. The route was withdrawn to `research/artifacts/unique-games-entangled-value-approximable-by-sdp-citation-2026-09-17.md`.
  Referee lens 1 returned *refuted*: B3 parts 2 and 3 use "x in L => val(O(x)) >= 1 - eta" and that `O` runs in polynomial time, but the B3 statement never assumes either (only `R` gets a completeness hypothesis); as written B3.2 is equivalent to P != NP (if P = NP, send every input to a fixed value-0 game and let `R` decide Gap-2to1 and output a fixed game, while `L` is outside P by the time hierarchy). Referee lens 2 returned *refuted*: the "dead as a class" bullet added to `rich-2to1-games-conjecture` overclaims, since KRT Theorems 1.3 and 4.5 need a unique game and KRT's only 2-to-1 result (Theorem 4.8) needs SDP value exactly 1; so nothing here rules out an entanglement-sound outer PCP to rich 2-to-1 games followed by the classically sound noise test, contradicting the claim's own "only composition left open" sentence. Lens 3 returned *survives* with the same missing-hypothesis caveat plus a midpoint-threshold remark for B1. All three lenses found B1, B2, the commuting-operator extension, C1--C4 and the KRT quotes sound, and `clifford_noise_test.py` passes.
