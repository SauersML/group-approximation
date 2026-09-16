---
rg: 2
id: braid-centralizer-characters-detect-infinite-order
kind: claim
title: Every infinite-order braid has infinite order in the abelianization of its centralizer
artifacts:
  - research/artifacts/braid-centralizer-characters-2026-09-16.md
---

**ESTABLISHED** by `braid-centralizer-characters-detect-infinite-order-proof`.

**Statement.** Let `n ≥ 1` and let `β ∈ B_n` have infinite order. Then `β` has
infinite order in `H_1(Z_{B_n}(β); Z)`. Equivalently, some homomorphism
`Z_{B_n}(β) → Q` is nonzero on `β`.

**The same holds in related groups.** The property "every infinite-order element
has infinite order in the abelianization of its centralizer" passes to
subgroups, to finite-index overgroups and to direct products. So it also holds
in:
- every subgroup of `B_n`;
- `B_n × Z^r`;
- `P_n / Z(P_n) ≅ PMod(S_{0,n+1})`;
- `B_n / Z(B_n)`;
- `Mod(S_{0,n+1})`.

**Consequence.** For each of these groups, the elements that are torsion in the
abelianization of their centralizer are exactly the elements of finite order.
- Bridson (arXiv:0908.0685, Proposition `l:hyp` and the proof of Theorem
  `t:paras`, cited by their LaTeX labels) shows that an
  isometry of a complete CAT(0) space with positive translation length has
  infinite order in the abelianization of its centralizer. For `Mod(Σ_g)`,
  `g ≥ 3`, the contrapositive forces Dehn twists to have translation length 0.
  That is the basis of Bridson's Theorem `t:paras`. With semisimplicity it
  recovers Kapovich–Leeb's result that `Mod(Σ_g)` has no proper semisimple
  action; whether Kapovich–Leeb's own proof uses this mechanism was not checked.
- For braid groups this criterion forces nothing: it applies only to
  finite-order elements.
- So an obstruction to `some-braid-group-has-no-proper-cat0-action`, or to
  `some-braid-group-is-not-cat0`, cannot start from zero translation length forced
  by abelian characters of centralizers.
- This claim produces no action; it removes one mechanism.

The artifact also records that `B_n` acts properly on a proper CAT(0) space iff
`Mod(S_{0,n+1})` does.
