---
rg: 2
id: fpbs-locally-free-malnormally-exhausted-finite-cost
kind: claim
title: Every free action of a malnormally exhausted locally free group with finite c* has finite cost
distinct_from:
  fpbs-locally-free-free-actions-have-finite-cost: that is the hole for all locally free groups; this is its only remaining case after fpbs-locally-free-wq-normal-fg-subgroup-fixed-price, namely groups where no finitely generated subgroup has malnormal hull equal to the group.
  fpbs-malnormal-subgroup-relations-finite-contacts: that is an obstruction to contact repair across almost malnormal subgroups; this is the open finite-cost statement in the class where that obstruction applies to every finitely generated anchor.
artifacts:
  - experiments/locally-free-finite-cost-2026-09-17/certs2.py
  - experiments/locally-free-finite-cost-2026-09-17/certs3.py
  - experiments/locally-free-finite-cost-2026-09-17/stallings.py
---

**OPEN.** Let `Gamma` be a countably infinite locally free group with
`c*(Gamma) < ∞` such that no finitely generated subgroup of `Gamma` has
malnormal hull `Gamma`. Prove that every free p.m.p. action of `Gamma` has
finite cost.

**Shape of the class.** By `fpbs-locally-free-wq-normal-fg-subgroup-fixed-price`
item 3, `Gamma = ∪ M_n` is a strictly increasing union of proper malnormal
subgroups, each of fixed price at most `c*`. So the statement is Tucker-Drob's
Q 7.6 (unions of relations of bounded cost) restricted to chains of malnormal
subgroups of bounded fixed price inside a locally free group. `Gamma_mal` is
in this class.

**Why the known tools stop here.**
- wq-normal absorption (`fpbs-wq-normal-subgroup-cost-transfer`) reaches exactly
  `W(H)`, which is proper for every finitely generated `H`.
- Contact repair from a subgroup orbit relation dies at the connectivity step
  whenever the anchor lies in a proper almost malnormal subgroup
  (`fpbs-malnormal-subgroup-relations-finite-contacts`), which is every
  finitely generated anchor here.
- Pseudocost and `beta_1` are already pinned to `c*`
  (`fpbs-locally-free-free-action-costs-are-c-star-or-infinite`).

## Attempts

**Short absorption certificates (September 17, 2026).** For one stage of
`Gamma_mal`, `Delta_0 = <a, cac^{-2}> <= Delta_1 = <a, c>`, add `c` on a small
set `A`. `c` is absorbed at `z` exactly when some word
`c = h_k c^(e_k) ... h_1 c^(e_1) h_0` (`h_i in Delta_0`) has all its `k`
intermediate points in `A`. Malnormality makes `h_0, h_k` unique given
`h_1..h_(k-1)`. Computation (`certs2.py`, `certs3.py`): there are exactly 3
two-letter certificates with `|h_i| <= 7` (`c = (cac^{-2}) c c a^{-1}`,
`c = (c^2a^{-1}c^{-1}) c a c^{-1}`, `c = c^{-1}(c^2a^{-1}c^{-1}) c a`), and 10
resp. 12 three-letter certificates with `|h_i| <= 5` resp. `6`. So there is no
infinite family of short parallel certificates, and the percolation heuristic
"infinitely many disjoint short certificates, so a sparse set hits one" fails at
length 2 and 3. This does not bound relative cost from below: each certificate
type contributes at most `mu(A)` absorbed mass, and there are infinitely many
types of growing length, so counting gives no obstruction either.
