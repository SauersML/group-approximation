---
rg: 2
id: toms-schubert-algebra-fails-o6-plus
kind: claim
title: In Toms's no-Gamma AH algebra, twisted equal-rank projections have no common Cuntz lower bound near full trace, so the Cuntz semigroup fails Thiel's (O6+)
distinct_from:
  toms-ah-counterexample-to-uniform-gamma: that imports B and its failure of uniform Gamma through non-equivalence of two projections of the tracial completion; this proves the Cuntz-level support gap for common lower bounds of the finite-stage pair and deduces failure of (O6+).
  toms-schubert-algebra-misses-a-rank: that asks whether some continuous rank is unrealized in B; this closes Thiel's stable-rank-one method on B and decides nothing about which ranks occur.
  uniform-gamma-iff-tracial-support-projections-and-division: that measures near projections under one positive element; this measures near projections Cuntz-below two equal-rank projections at once.
  toms-schubert-algebra-has-no-small-joins: that bounds common Cuntz upper bounds of the same pair from below and gives failure of (O6+) or of weak cancellation; this bounds common lower bounds away from full trace and gives failure of (O6+) with no disjunction.
artifacts:
  - research/artifacts/toms-schubert-o6-plus-failure-2026-09-12.md
---

Let `B = lim (B_i, psi_i)` be Toms's simple AH algebra without uniform property
Gamma (arXiv:2606.12188v2, Proposition 4 and Theorem 5). Let `p_m, q̂_m in M_k(B_m)` be
the old obstruction projections, with equal constant rank, and let `delta > 0` and
`eta_m = sum_(r >= m) (1 - alpha_r)` be the survival data of Proposition 4. Put
`h_eps(t) = min(1, max(0, (t - eps)/eps))`.

**Theorem A (support gap).** If `sqrt(eta_m) <= delta/(2 sqrt k)`, then every
`c in (B tensor K)_+` with `c <~ p_m` and `c <~ q̂_m` satisfies, for every `eps > 0`,

```text
sup_(tau in T(B)) ( d_tau(p_m) - (tau tensor Tr)(h_(2 eps)(c)) )  >=  delta^2 / 8.
```

**Corollaries.**
- **B.** No nonzero common lower bound `c` of `p_m` and `q̂_m` has a continuous rank
  function within `delta^2/8` of `d(p_m)`. In particular none has `d(c) = d(p_m)`.
- **C.** `Cu(B)` does not satisfy Thiel's strengthened almost Riesz decomposition
  (O6+). Otherwise Thiel's Theorem 7.5 (CMP 377, 2020) would produce
  `c <= [p_m], [q̂_m]` with `d(c) = d(p_m) ∧ d(q̂_m) = d(p_m)`, contradicting B.
- **D.** `B tensor K` does not have almost stable rank one, by Thiel's Theorem 6.4
  and Remark 6.5. In particular `sr(B) >= 2`, recovered without Vaccaro's theorem.
- **E.** Thiel's proof that all ranks occur (Theorem 8.11 through Theorems 7.5 and
  8.7) cannot run on `B`. A proof of STW XXIII for `B` must avoid attained infima
  below given elements.

The obstruction itself is Toms's: total degeneracy of every bundle map
`p_n -> q_n` from a nonzero Thom–Porteous class, and survival of point masses.
What is new is the passage from a common Cuntz lower bound with small support gap
to an approximate uniform 2-norm equivalence between `p_m` and `q̂_m`, via
Rørdam's lemma and functional calculus, and the Cuntz-semigroup consequences.
Internal derivation, unreviewed.

This does not show that any rank is unrealized in `B`.
