---
rg: 2
id: fpbs-certificate-budget-premise-is-equivalent-to-goal-proof
kind: route
title: The strong converse has no collapse hypothesis, so a premise that contradicts it is threshold separation
target: fpbs-certificate-budget-premise-is-equivalent-to-goal
requires:
  - fpbs-bounded-query-connection-strong-converse
  - fpbs-optimistic-search-certified-growth
artifacts:
  - research/artifacts/fpbs-certificate-budget-premise-equivalence-2026-09-17.md
---

The artifact proves the claim in Sections 2 through 5.

**Step 1.** A returned path is a certificate of o<->X_n using at most
floor(b n) fresh queries. For the optimistic search this is
`fpbs-optimistic-search-certified-growth`; for other admissible searches it
holds by definition.

**Step 2.** The strong converse bounds the probability of such a
certificate by exp(-eta n). Its hypotheses are only 0<c<q<1, a seed
independent of the percolation, the same rule under c and q, and the
critical walk correlation. Collapse is not among them, so the success rate
is at most -eta on every graph.

**Step 3.** The premise asserts success rate 0 under collapse. It therefore
forbids collapse, and it holds vacuously when p_c<p_u.

**Step 4.** Loop edges change no cluster, so the hole's range of Cayley
graphs and the goal's range give the same threshold statements.

**Weakenings.** Subsequences are covered because the converse bounds every
n. Conditioning on infinite endpoints costs a factor theta(q)^2>0, by
Harris--FKG and theta(q)>0 above p_c=p_u. Expected-cost premises reduce to
capped success by Markov's inequality at an intermediate budget b'.

**Class kill.** An implication into an everywhere-false conclusion has an
unsatisfiable antecedent.
