---
rg: 2
id: pauli-norm-games-qpcp-needs-imperfect-completeness
kind: claim
title: A Pauli energy test whose soundness error exceeds 2+sqrt2 times its completeness error decides only NP problems
artifacts:
  - research/artifacts/pauli-frustration-stabilizer-rounding-2026-09-12.md
distinct_from:
  quantum-games-pcp-for-qma: that is the open conjecture about succinct efficient-prover MIP* protocols for QMA; this is an NP upper bound on the Hamiltonian families that the standard Pauli energy test can use, stated for the test's own completeness and soundness errors.
  natarajan-vidick-games-pcp-amplification-error: that records the source error and the corrected amplification lemma; this proves which inputs to that lemma are already in NP.
---

**ESTABLISHED (ordinary proof, unreviewed).** For an explicit Pauli decomposition
`H = sum_P beta_P P` of weight `W = sum|beta_P|`, the energy test of
arXiv:2403.13084v1 (Section 4.2) samples `P` with probability `|beta_P|/W`,
measures `P`, and accepts iff the outcome equals `sign(beta_P)`. Its acceptance
probability on a state `rho` is `1/2 + tr(H rho)/(2W)`.

1. **(GT1)** Consider a family of such decompositions with a promise: on YES
   instances some state passes the test with probability at least `1-eps_c`; on NO
   instances every state passes with probability at most `1-eps_s`. If
   `eps_s > (2+sqrt2) eps_c`, the promise problem is in NP.
2. **(GT2)** The corrected amplification lemma of that note (Lemma 6, Section 4.3) takes
   `-I <= H <= I` with promise `lambda_max >= 1-1/p` versus `<= 1-1/q`. If the
   input decompositions have weight at most one, the case `p > (2+sqrt2)q` is in
   NP. The lemma's energy test on its output has acceptance gap at least
   `(1-(1+ln r)/r)/3` with `r = p/q` (at `k = 2q ln r`), which is positive for every
   `r>1`. So unless QMA is in NP, open problem 1 of the note (a QMA-complete
   bounded-norm input family for the lemma) can only be answered in the window
   `1 < p/q <= 2+sqrt2`.

Perfect completeness of the energy test (`eps_c = 0`) forces all `sign(beta_P)P`
to share a `+1` eigenvector. That is a commuting consistent Pauli system, decidable
in polynomial time. Games protocols built on this test therefore need completeness
error inside the energy test comparable to its soundness gap. The other parts of a
protocol (code and low-degree tests) are not constrained by this claim.
