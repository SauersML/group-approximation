---
rg: 2
id: trappable-unitary-commutator-seeds-of-every-depth
kind: claim
title: For every c, c-fold unitary commutators with nonzero reduced Spin_m-bordism class exist in U(N) for unboundedly many N
distinct_from:
  simple-cstar-unitary-component-group-not-nilpotent: That is the C*-algebra existence problem; this is the finite-stage bordism input that the glued trapping towers need.
  unitary-word-transfer-to-simple-ah-via-trapping: That transfers one visible word into a simple algebra; this asks for visible commutators of every depth in growing ranks.
artifacts:
  - research/artifacts/class-four-lambda-mod-eight-trapping-part3-2026-09-13.md
---

**OPEN.** For every c >= 2 there are m >= 1 and an unbounded set S_c of
integers with the following property. For each N in S_c, some closed
Spin_m-manifold M and some unitaries u_1, ..., u_{c−1}, v in C(M, M_N) have

    f = [u_{c−1}, [..., [u_1, v]...]]   with   [M, f]_red != 0
    in Omega-tilde^{Spin_m}_{dim M}(U(N)).

With the transfer and gluing of Part 3, Section 9, this would give a simple
unital AH algebra with a non-nilpotent unitary component group.

## Attempts

- *Protected rank two.* Capped. Depths c = 3, 4 work for N = 2 only
  (Parts 1–2 and the class-three tower). Spin bordism is blind at c = 4 on
  every seed manifold (rank-two-spin-trapping-blind-to-depth-three-brackets).
  Every bordism detector is blind at c = 5 for sphere-product seeds
  (rank-two-trapping-blind-to-fivefold-sphere-commutators). Stabilizing a
  rank-two seed kills it: 6 nu' in pi_6 U(2) maps to 0 in pi_6 U(3) ≅ Z/6.
- *m = 1 in any rank.* Dead for c >= 4. Spin bordism kills every fourfold
  commutator of U(N)-valued maps, for every N and every seed manifold
  (spin-trapping-blind-to-fourfold-commutators-in-every-rank). So for
  c >= 4 the structure must have m >= 2.
- *Odd primes need rank above p.* The witness has finite order. So,
  arXiv:1707.00739v2 p. 1, quotes two results. p-regular Lie groups have
  homotopy nilpotence class at most 3 (Kaji–Kishimoto), and quasi-p-regular
  SU(n) with p >= 7 do too (Kishimoto). So for c >= 4, the p-primary part of
  a c-fold commutator of SU(N)-valued seeds vanishes whenever p >= N. It
  must come from p = 2 or from primes p < N.
- *Unbounded N is not known even for small c.* No c-fold visible commutator
  in U(N) with N >= 3 is known to this lane, for any c >= 2.
- *Bott brackets.* <a_i, a_j> = (i−1)!(j−1)!·g in pi_{2N} U(N) has odd
  coefficient only for N <= 3. For odd N the evaluation U(N) -> S^{2N−1}
  kills pi_{2N} U(N). So the stem-one reading dies at the first bracket for
  N >= 3.
- *Where it may die.* Toward a cap, heuristic only. KO-type and e-invariant
  detectors see products with at most three factors eta, and image-of-J
  products vanish at odd primes. Visible depth may therefore be bounded
  independently of N. That is not proved.
- *Unexplored.* Brackets detected in stems 6 (nu^2) or 10 (eta·mu_9), tmf-type
  structures on TX − W_R, and non-spherical seeds in rank three or four.
