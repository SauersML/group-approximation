---
rg: 2
id: cp-failures-transfer-between-hyperbolic-and-leh-groups
kind: claim
title: CP, CP_col and NPE fail at some hyperbolic group iff they fail at some local limit of hyperbolic groups iff one fixed Kazhdan hyperbolic group has a finite-quotient-free hyperbolic quotient where they fail, and no such transfer reaches the universal tester
distinct_from:
  nonsofic-hyperbolic-question-reduces-to-one-fixed-host: that is the same reduction for soficity and the metric approximation properties; this is the reduction for the symbolic-dynamical properties CP, CP_col and NPE, where closedness comes from finite partial-table witnesses instead of metric tables, and it adds the obstruction at the tester.
  cover-pair-failures-have-finite-partial-table-witnesses: that proves locality and gives the all-group tester; this combines locality with Olshanskii quotients for hyperbolic hosts, and shows that the all-group tester lies outside the reach of hyperbolic and finite models.
  hyperbolic-local-embedding-kills-compression-certificates: that shows that the nonsoficity certificates of the graph vanish on LEH groups; this uses its Thompson-group consequence to place the tester outside LEH.
---

**ESTABLISHED** through [[cp-failures-transfer-between-hyperbolic-and-leh-groups-proof]].

Let `P` be `CP`, `CP_col` or `NPE`, as defined in `cover-pair-failures-have-finite-partial-table-witnesses`. Let
`T` be a non-elementary word-hyperbolic group with trivial maximal finite normal subgroup. The following are
equivalent.

1. `P` fails at some word-hyperbolic group.
2. `P` fails at some LEH group (definition in `hyperbolic-local-embedding-kills-compression-certificates`). This
   class includes:
   - marked limits of hyperbolic groups;
   - lacunary hyperbolic groups;
   - the free Burnside groups `B(m, N)` of large odd exponent (`free-burnside-is-a-limit-of-hyperbolic-groups`).
3. For every finite `M ⊆ T` there is a surjection `π : T → Q`, injective on `M`, such that `Q` is a
   non-elementary hyperbolic group, `P` fails at `Q`, and `Q` has no nontrivial finite quotient.
4. `P` fails at some hyperbolic quotient of `T`.

**Kazhdan host.** Take `T` torsion-free, non-elementary, hyperbolic and Kazhdan
(`torsion-free-hyperbolic-kazhdan-partner-exists`).
- A hyperbolic counterexample to CP, or to its non-Gottschalk part `CP_col`, exists iff this one group has a
  hyperbolic quotient that is a counterexample.
- Such a quotient can be taken Kazhdan and finite-quotient-free.
- In particular, CP holds at every LEH group iff it holds at every hyperbolic quotient of one fixed Kazhdan
  lattice.

**Obstruction at the tester (class kill).** Let `U` be the all-group tester of
`universal-all-group-subgroup-colimit-class-tester`. By `cover-pair-failures-have-finite-partial-table-witnesses`,
`P` holds for all groups iff `P(U)` holds.
- `U` is not LEH and not LEF. It contains Thompson's group `F`, and no LEH group contains `F` (Consequence 1 of
  `hyperbolic-local-embedding-kills-compression-certificates`). Every LEF group is LEH, since finite groups are
  hyperbolic.
- *Killed class: model transfer.* This means proving `P` on a class `C` of model groups and moving it along partial
  embeddings (Theorem L), marked limits or colimits. Such a transfer reaches all groups iff `U` is locally
  embeddable into `C`. So every model transfer with `C` equal to the finite, residually finite, LEF, hyperbolic or
  LEH groups stops before `U`.
  - *Invariant:* local embeddability into `C`. It passes to subgroups and marked limits, and a transfer along
    partial embeddings never leaves it.
  - *Dying step:* the Thompson subgroup `F ≤ U`. It contains the commuting pair `F × F` of non-LEF groups, which
    Theorem B of that claim excludes in LEH groups.
  - *Remark (not load-bearing).* The same wall is visible as a universal sentence. For
    `ψ : ∀x,y (x y^2 x^-1 = y^3 → [x y x^-1, y] = 1)`:
    - `ψ` holds in every finite group. There `y^2` and `y^3` have equal orders, which forces `y` to have order
      prime to 6, so `y` is a power of `y^2`.
    - It holds in every hyperbolic group, by the same argument once infinite-order `y` is excluded. That
      exclusion uses the standard positivity of stable translation length, which is not imported here.
    - Universal sentences pass along partial embeddings.
    - `ψ` fails in `BS(2,3) ≤ U`: `x = t`, `y = a`, and Britton's lemma.
- So, as far as locality can tell, "CP holds at every hyperbolic group" leaves CP over all groups open. A proof
  over all groups needs a model class into which `U` locally embeds, for example a class containing the finitely
  presented groups, or a non-local argument.

**What this changes.** The hyperbolic and Burnside corner of CP and `CP_col` becomes one question about quotients
of one Kazhdan lattice. The remaining gap for model-transfer methods is `U`, and the obstruction there has a
name.
