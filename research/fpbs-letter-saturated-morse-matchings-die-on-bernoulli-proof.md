---
rg: 2
id: fpbs-letter-saturated-morse-matchings-die-on-bernoulli-proof
kind: route
title: Global heights make each letter's sublevels almost invariant under the per-type transport group up to the letter's unmatched-or-elsewhere mass; the single-letter Kesten argument then caps every letter share
target: fpbs-letter-saturated-morse-matchings-die-on-bernoulli
requires:
  - kesten-amenable-stabilizer-uniform-gap
  - fpbs-bernoulli-morse-collapse-criterion
  - fpbs-single-letter-morse-matchings-die-on-bernoulli
artifacts:
  - research/artifacts/fpbs/docs/letter-saturated-morse-obstruction.md
  - experiments/letter-saturated-morse-2026-09-17/lockstep_barrier.py
---

The written proof is given in full in Sections 2-4 of the artifact.

1. **Global heights.** Kept edges of every letter have height `0`. A removed edge has height `1 +` the maximum height
   of the other removed edges of its cell, of any letter. By (M3) and König's lemma, heights are finite a.e.
   *Top property:* the matched edge is strictly highest in its cell.
2. **Lemma 1'.** A type-`r` cell matched with `ht(M(y)) <= j` is s-inside the sublevel `A_j^s`. Counting type-`r`
   incidences gives `beta_j <= k (n_j - I_j) <= k tau_rs(j) <= k eps_rs`, where `eps_rs = 1 - mu(r -> s)`.
3. **Lemma 2'.** For `q in Q_rs`, `mu(A_j Δ q A_j) <= 2 k eps_rs`. This is the argument of
   `fpbs-single-letter-morse-matchings-die-on-bernoulli`, run on type-`r` cells.
4. **Lemma 3'.** An `s`-edge of height `J` has `>= k - 1` type-`r` incidences from cells not matched to it. Each such
   cell is either unmatched, or matched to a non-`s` edge of height `> J`, or matched to an `s`-edge of height `> J`.
   This gives `(k - 1) mu{ht = J} <= k(eps_rs + 1 - n_J)`.
5. **Gap and conclusion.** Lemma 4 of the single-letter proof applies to `Lambda_rs`, and it rests on (KAG2) of
   `kesten-amenable-stabilizer-uniform-gap`. Since `n_0 <= eps_rs`, Section 4 of the single-letter proof applies with
   `delta := eps_rs`, which gives `eps_rs >= (k - 1)(1 - rho)/(6 k^2)`.
6. **Proposition D.** Put `u = lambda^j/|T|`. Then `tau = (|T| - 1) u >= u`, so (I2) follows from `u(1 - u) <= u`.
   (I3) reduces to `(k - 1)(1 - lambda) <= k |T| lambda`. The script checks this in exact arithmetic and exits 0.
