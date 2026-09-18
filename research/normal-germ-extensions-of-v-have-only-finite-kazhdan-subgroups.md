---
rg: 2
id: normal-germ-extensions-of-v-have-only-finite-kazhdan-subgroups
kind: claim
title: In the germ regime of Belk--Hyde--Matucci Corollary 2.10, finite germ extensions of V have no infinite Kazhdan subgroups
distinct_from:
  normal-germ-extensions-of-thompson-v-contain-no-sl3z: that excludes finite-index subgroups of SL_3(Z) from the same regime, using Margulis's normal subgroup theorem and a non-abelian nilpotent subgroup; this excludes every infinite group with property (T), with property (T) doing all the work.
  almost-v-fw-subgroups-act-through-finitely-many-germs: that reduces a Kazhdan subgroup of any finite germ extension of V to finitely many germ groups; this shows that in the Corollary 2.10 regime those germ groups have no infinite Kazhdan subgroups, so nothing is left.
  kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf: that proves Kazhdan subgroups of Rover--Nekrashevych groups residually finite; for bounded automata groups, which lie in this regime, this upgrades residually finite to finite.
---

**ESTABLISHED** by `normal-germ-extensions-finite-kazhdan-proof` (referee-a PASS, research/artifacts/gq-referee-a-kazhdan-almost-v-central-and-normal-germ-extensions.md, bdc9e959c; lane proof, short, from
landed nodes; citation review by referee-b pending; no novelty claimed beyond the generalization of
Theorem B of `normal-germ-extensions-of-thompson-v-contain-no-sl3z`).

**Setting.** `V` acts on `C = {0,1}^N`, and `V <= G <= Homeo(C)` is a finite germ
extension of `V` in the sense of Belk--Hyde--Matucci (arXiv:2407.03149). Suppose every
`p in sing(G)` satisfies
- (a) `|(G)_p : (V)_p| < ∞`, or
- (b) `p` has an eventually periodic address and `(V)_p` is normal in `(G)_p`.

These are the two alternatives of the germ hypothesis of Corollary 2.10 there, with (b)
restricted to periodic points, as in Theorem B of
`normal-germ-extensions-of-thompson-v-contain-no-sl3z`.

**Theorem.** Every subgroup of `G` with property (T) is finite.

## Consequences

**Named hosts in the regime.** By Corollary 2 of
`normal-germ-extensions-of-thompson-v-contain-no-sl3z`, the hypotheses hold for:
- `VA`, and so for its subgroup `T̄` containing `Q`;
- every binary Rover--Nekrashevych group `V_2(G)` of a bounded automata group `G`, such as
  Rover's group over the Grigorchuk group.

So every Kazhdan subgroup of these groups is finite. For the Rover--Nekrashevych case this
upgrades `kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf` from residually finite to
finite, for bounded automata.

Each of the following contains an infinite Kazhdan subgroup, so none embeds in such a `G`:
- `SL_n(Z)` for `n >= 3` and every group containing a finite-index subgroup of one,
  including `GL_n(Q)`, `n >= 3` (this recovers Theorem B there);
- `Sp_2n(Z)` for `n >= 2`, and the Deligne lattice `Gamma~`
  (`deligne-lattice-satisfies-boone-higman`);
- `Aut(F_n)` and `Out(F_n)` for `n >= 5`, which have property (T) (Kaluba--Nowak--Ozawa for
  `n = 5`, Kaluba--Kielak--Nowak for `n >= 6`; cited, not re-read). So this regime cannot
  answer BBMZ Problem 5.3(3) for these `n`;
- every infinite simple Kazhdan group. By `boone-higman-iff-simple-kazhdan-decidable-inputs`,
  a proof of `boone-higman-conjecture` through finite germ extensions of `V` must, for every
  such input, leave the Corollary 2.10 regime at some singular point. That means an
  aperiodic singular point with infinite germ group, or germs at a periodic point that do
  not normalize the local dilation.
  - An aperiodic singular point already defeats Theorem 2.1. There
    `SingFix(∅,{p}) = Fix_V(p)` is a strictly increasing union of pointwise stabilizers of
    shrinking cones, so it is not finitely generated
    (`orbit-preserving-germ-corollary-extensions-of-v-are-rational`, intermediate fact 1).
  - So a Theorem-2.1-certified host of an infinite simple Kazhdan input `S` has all its
    singular points eventually periodic. By `bhm-singfix-condition-forces-fp-germ-groups`
    and `simple-kazhdan-in-germ-extension-of-v-sits-in-one-germ-group`, it carries `S` in
    one finitely presented germ group `(G)_y` at a periodic point. By Step 1 of the proof
    route, the normalizer there of the `V`-dilation contains no infinite Kazhdan subgroup,
    so no finite-index subgroup of `S` normalizes it. Shell envelopes have exactly this
    shape.

## Scope

- The base is the binary `V`, the setting of the FW germ reduction.
- Case (b) at aperiodic points is not covered: there `(V)_p = 1` and normality is vacuous.
- Nothing is said about finite presentation or about groups without property (T).
