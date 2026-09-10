---
rg: 2
id: fpbs-two-generator-action-cost-witness
kind: claim
title: Every free action of cost above one has a two-generated subgroup restriction of cost above one
root: true
---

**Statement.** Theorem 6.2 of the two-generator note: let G be countably infinite and alpha a free
p.m.p. action. If C(alpha restricted to <g,h>) <= 1 for all g,h in G, then C(alpha)=1. Equivalently,
a free action of cost above one has a two-generated subgroup whose restriction already has cost above
one. The implication is not reversed, and the witness subgroup is not asserted to fail fixed price.

The proof is a three-way case split at the level of the one specified action. Bounded exponent and
finitely generated: an infinite two-generated subgroup gives cost one by hypothesis and the transfer
theorem applies; otherwise every two-generated subgroup is finite and the binary-finite lemma supplies
an infinite abelian subgroup, which is locally finite and so has cost one. Finitely generated without
bounded exponent: elements of order at least M exist for every M, giving 1 <= C(alpha) <= 1+(d-1)/M
for a d-element generating set, then let M grow. Countably generated: locally finite groups have
cost-one free actions, and otherwise an increasing exhaustion by finitely generated subgroups is glued
with summable relative costs.

**Proof location.** `research/artifacts/fpbs/two-generator-complete-proof.md`, Theorem 6.2 and its
Steps 1 to 3; responses 14 and 15.

**Imported inputs.** Gaboriau, arXiv:1011.2294v1, standard and relative cost facts, and the amenable
cost theorem. Ershov-Golan-Sapir, *The Tarski numbers of groups*, arXiv:1401.2202, Theorem 5.6 and
Lemma 5.7; Step 2 is their high-order-element argument made action-wise. Suchkova-Shunkov, as stated
in Chernikov, arXiv:0711.2597v1. All identifiers resolve; the Chernikov note does state the
Suchkova-Shunkov theorem, so the attribution is accurate even though the arXiv author is Chernikov.

**Finite-replay evidence.** `two-generator-proof-audit.json` reuses
`bounded-exponent-reaudit-checks.json` (PASS, 48,584 exact assertions, 5,952 exhaustive colorings) and
adds `cyclic-section-checks.json` via `scripts/replay_cyclic_sections.py` (PASS, 5,060 assertions over
565 finite graphing cases on C_3, C_6, C_2^3, D_8, Q_8, S_3, A_4 and S_4).

**Evidence level.** Written deduction with named published inputs and a passing finite replay of the
selection, collision and normalization steps. Not refereed, not formally verified. This is one of the
two results the later documents explicitly firewall: `torsionfree-local-audit.json` lists "Previous
two-generator cost theorem" among the things it does not assume, and `explicit-window-audit.json`
lists "earlier broad two-generator or bounded-exponent cost deductions" among the things its proof does
not use. Neither says the theorem is wrong. Nothing written after response 15 depends on it.
