---
rg: 2
id: some-group-has-isomorphic-bernoulli-shifts-of-different-entropy
kind: claim
title: Some countably infinite group has isomorphic Bernoulli shifts whose bases have different Shannon entropy
distinct_from:
  bernoulli-shift-entropy-classifies-for-every-group: that is the universal classification; this is its negation, the existence of one group where it fails.
  bernoulli-isomorphism-collapse-set-is-a-subgroup: that proves the structure of the collapse subgroup D(G) on every group; this asks that D(G) be nonzero for one group.
---

**OPEN.** There is a countably infinite group `G` and standard probability spaces `(L, lambda)`, `(K, kappa)`
with `H(L, lambda) != H(K, kappa)` such that `G ↷ (L^G, lambda^G)` and `G ↷ (K^G, kappa^G)` are isomorphic.
Equivalently, `D(G) != {0}` in `bernoulli-isomorphism-collapse-set-is-a-subgroup`.

This is the negation of `bernoulli-shift-entropy-classifies-for-every-group`. Seward, arXiv:1805.08279v1,
introduction: "if non-soﬁc countable groups G exist, then it is still unknown whether (2^G,u_2^G) and
(3^G,u_3^G) are isomorphic."

Necessary conditions on `G` are in `bernoulli-entropy-counterexample-constraints`: `G` is nonsofic, its
Rokhlin supremum is small, and failure passes to supergroups.

## Attempts

- **Algebraic absorption plus co-induced Ornstein.** Dead:
  - a stable finiteness failure makes a Bernoulli shift absorb an algebraic factor `X_P`
    (`stable-finiteness-failure-is-algebraic-bernoulli-absorption`);
  - co-induced summands can be turned into Bernoulli entropy
    (`coinduced-finite-subgroup-shifts-add-entropy-to-bernoulli`);
  - but the entropy added is the lifted p-adic trace, which module isomorphisms conserve
    (`finite-subgroup-induced-absorption-conserves-entropy`, invalidating
    `leavitt-induced-absorption-gives-bernoulli-collapse`).

  A live version needs an absorbed summand whose dual action is Bernoulli with entropy different from its
  lifted trace. For an absorbed summand the lifted trace is `0`.
- **Leavitt doubling.** Dead as a Bernoulli source. `L ≅ L ⊕ L` gives a free ergodic self-square `X_L ≅ X_L²`
  over the unit group. No Leavitt-module dual action is a Bernoulli factor
  (`leavitt-module-dual-actions-are-self-squares-off-bernoulli`).
- **Seward-type relative isomorphisms.** They preserve a common factor, and the recoding along an amenable
  subrelation needs equal row entropy (`research/artifacts/bernoulli-negative-coinduced-ornstein-2026-09-12.md`,
  Step 4). A collapse must mix rows or change the common factor.
