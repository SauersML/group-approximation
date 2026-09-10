---
rg: 2
id: fpbs-adaptive-exploration-entropy-proof
kind: route
title: Sum conditional query divergences and pass through stopped prefixes
target: fpbs-adaptive-exploration-relative-entropy
requires: []
artifacts:
  - research/artifacts/fpbs/exploration-information.md
---

Section 1 supplies the sequential entropy proof. Each fresh edge remains
Bernoulli with its original parameter conditional on the transcript.
Capping after M queries gives exactly k(q,c)E_q[min(N,M)]. Prefix entropy
convergence and monotone convergence handle unbounded stopping. Grouping
by the output bit and convexity of t log t give data processing.
