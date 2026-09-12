---
rg: 2
id: fpbs-bs-via-generating-set-invariance
kind: route
title: Transfer one good simple generating set to all generating sets
target: fpbs-benjamini-schramm-universal
requires:
  - fpbs-nonuniqueness-phase-is-a-group-invariant
  - fpbs-simple-generating-set-with-gap-exists
---

Let `Gamma` be nonamenable and let `S` be any finite symmetric generating set.
- `fpbs-simple-generating-set-with-gap-exists` supplies a generating set `S_0`
  with `p_c < p_u` on `Cay(Gamma,S_0)`.
- `fpbs-nonuniqueness-phase-is-a-group-invariant` transfers the nonuniqueness
  phase to `Cay(Gamma,S)`.

Conversely, the target implies both premises. For amenable groups the first
premise is vacuous, because no Cayley graph of an amenable group has two
infinite clusters. So the route is an exact decomposition: its premises are
Choi--Seo's Question 1.2 and Juschenko--Nagnibeda's question, with no loss.
