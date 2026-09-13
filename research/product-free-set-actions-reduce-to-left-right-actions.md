---
rg: 2
id: product-free-set-actions-reduce-to-left-right-actions
kind: claim
title: Every set action of a product of free groups is sofic once the Goursat quotient of its stabilizer is left-right sofic
distinct_from:
  mikhailova-left-right-action-current-frontier: that records what is known about the left-right action of one quotient; this proves that the left-right actions of all groups control every set action of every product of two free groups, including stabilizers with non-full projections.
  separating-sofic-quotient-sets-make-an-action-sofic: that proves (C3), full-projection Mikhailova stabilizers over residually amenable quotients; this treats arbitrary stabilizers through Goursat's lemma and a Marshall Hall retraction.
  mikhailova-left-right-action-sofic-for-lea-quotients: that constructs models for LEA quotients; this is the reduction and the closure properties of the class, which recover the LEA case as a marked-group limit.
artifacts:
  - research/artifacts/pfg-positive-goursat-reduction-2026-09-13.md
---

ESTABLISHED (unreviewed). Soficity is GKP Definition 2.1(5).

**Left-right sofic groups.** Let `Q` be countable, with epimorphisms
`q_1 : F ↠ Q` and `q_2 : F' ↠ Q` from countable free groups. The left-right
action is

```text
LR(q_1,q_2) :  F x F' ↷ Q,       (u,v).h = q_1(u) h q_2(v)^-1.
```

`Q` is *left-right sofic* if every `LR(q_1,q_2)` is sofic. For finitely
generated `Q` this is the same as soficity of the Mikhailova action (MLF1) of
[[mikhailova-left-right-action-current-frontier]] for one presentation. The
following hold:

- amenable groups are left-right sofic;
- the class is closed under subgroups and finite direct products;
- the class is local: `Q` belongs iff its finitely generated subgroups do;
- the class is closed under marked-group limits, so it contains LEA.

**Theorem (Goursat reduction).** Let `G = F x F'` with `F`, `F'` countable
free, and `L <= G` any subgroup. By Goursat's lemma,
`L = { (a,b) in A x B : rho_1(a) = rho_2(b) }` with `A`, `B` the projections of
`L` and `rho_i` epimorphisms onto the Goursat quotient `Q_L`. If every finitely
generated subgroup of `Q_L` is left-right sofic, then `G ↷ G/L` is sofic.

**Corollary (equivalence).** The following are equivalent:

- [[product-of-free-groups-set-actions-are-sofic]];
- every countable group is left-right sofic;
- (MLF1) is sofic for every finitely presented group.

So one finitely presented group with a nonsofic (MLF1) refutes the target. In
particular, the fixed nonsofic property-(T) quotient left open by the frontier
node is a special case of the target.

**Mechanism.** In a finite window take `L_R = < L ∩ ball >` and
`L^+ = L ∩ (p_1(L_R) x p_2(L_R))`. `L^+` is a full-projection fibre product over
a finitely generated subgroup of `Q_L`. Marshall Hall's theorem makes
`p_1(L_R)` a free factor of a finite-index subgroup, and the retraction pulls
`L^+` back to `K`, with `K ∩ (A_R x B_R) = L^+`. The window then embeds partially
equivariantly into `G/K x G/(A_R x B_R)`. That product is sofic by finite-index
induction, GKP 2.19 and (S2). Local separation finishes.

DERIVATION [[product-free-set-actions-reduce-to-left-right-actions-proof]].
