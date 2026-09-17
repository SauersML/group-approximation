---
rg: 2
id: weakly-minimal-oe-transfers-rokhlin-supremum
kind: claim
title: Orbit equivalence of weakly minimal free actions transfers the Rokhlin entropy supremum, and a stable weakly minimal relation forces zero or infinity
distinct_from:
  rokhlin-supremum-dichotomy-with-centralized-self-copies: that forces the zero-or-infinity dichotomy from centralized finite subgroups inside the group; this forces it from stability of the orbit relation of one weakly minimal free action, with no subgroup hypothesis, and adds transfer of the supremum between different groups.
  paunescu-orbit-equivalent-free-actions-share-soficity: that transfers soficity along orbit equivalence; this transfers the Rokhlin supremum along orbit equivalence of actions weakly contained in all free actions.
  seward-per-group-rokhlin-entropy-of-bernoulli-shifts: that is Seward's per-group computation and his product vanishing theorem; this uses them to compare different groups through a shared measured relation.
artifacts:
  - research/artifacts/bernoulli-bundle-orbit-relation-entropy-2026-09-17.md
---

**ESTABLISHED (unreviewed)** by [[weakly-minimal-oe-transfers-rokhlin-supremum-proof]].

Call a free p.m.p. action **weakly minimal** if it is weakly contained in all free p.m.p. actions of its
group. Let G and Γ be countably infinite groups.

1. **Upper transfer.** If a weakly minimal free G-action is orbit equivalent to some free Γ-action, then
   `h_sup(G) <= h_sup(Γ)`.
2. **Equality.** If a weakly minimal free G-action is orbit equivalent to a weakly minimal free Γ-action,
   then `h_sup(G) = h_sup(Γ)`. Hence INF, RBS and POS hold for G if and only if they hold for Γ.
3. **Stability dichotomy.** If some weakly minimal free G-action Y has `R_Y ≅ R_Y × R_0`, where R_0 is the
   ergodic hyperfinite relation, then `h_sup(G) ∈ {0, ∞}`.

**Use.** Item 2 lets RBS, and with it Gottschalk and Kaplansky for the group (Seward, Corollary 4.1), be
imported from any group whose weakly minimal actions share an orbit relation with G's. Item 3 gives the
dichotomy from a property of one measured relation.

**Limitation on `U_*`.** By `paunescu-orbit-equivalent-free-actions-share-soficity` and
`free-action-containing-nonsofic-group-relation-is-nonsofic`, every free action orbit equivalent to a free
`U_*`-action is a nonsofic action. So item 2 cannot import INF from a group certified through sofic
approximations, unless weakly minimal actions of such groups can be nonsofic. The details are recorded on
`tester-host-has-positive-rokhlin-entropy-action`, under Attempts.
