---
rg: 2
id: fpbs-adaptive-exploration-relative-entropy
kind: claim
title: A stopped adaptive edge transcript has entropy equal to the Bernoulli divergence times its expected query count
artifacts:
  - research/artifacts/fpbs/exploration-information.md
---

Section 1: for the same adaptive algorithm under Bernoulli-c and
Bernoulli-q, using fresh queries and a parameter-independent seed and
halting almost surely under both laws, the transcript relative entropy
is k(q,c) E_q N, with infinity allowed. Binary output entropy is at most
this quantity. A prefix chain rule and the stopped-transcript limit
give the proof without assuming E_c N is finite.
