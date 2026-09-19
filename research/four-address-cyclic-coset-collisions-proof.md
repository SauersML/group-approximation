---
rg: 2
id: four-address-cyclic-coset-collisions-proof
kind: route
title: Kill each blocking partition by one cyclic subgroup whose coset partition makes the indicator collide with a constant
target: four-address-cyclic-coset-collisions-exclude-89-survivors
requires:
  - binary-four-address-single-flip-balance-census
  - amenable-groups-satisfy-the-garden-of-eden-theorem
  - bijective-ca-preserve-uniform-bernoulli-measure
artifacts:
  - experiments/gottschalk-four-address-coset-collisions-2026-09-17/coset.py
  - experiments/gottschalk-four-address-coset-collisions-2026-09-17/coset.json
  - experiments/gottschalk-four-address-coset-collisions-2026-09-17/control.py
  - experiments/gottschalk-four-address-coset-collisions-2026-09-17/control.out
---

1. **Import the survivors.** By `binary-four-address-single-flip-balance-census`, an injective unbalanced rule
   is one of 195 classes. Its group either has an amenable memory group, or realizes a coarsening of one of the
   rule's blocking partitions `P` (`analyze3.json`, key `survivors`).
   - The amenable case is balanced by `amenable-groups-satisfy-the-garden-of-eden-theorem` and
     `bijective-ca-preserve-uniform-bernoulli-measure`.
   - Symmetries do not matter. The test below runs over all pairs `(i, j)` and both complement versions, so it is
     invariant under address permutations and under input and output complement.
2. **Lemma.** The cyclic-coset collision lemma of the target, proved there in full.
3. **Forced partition.** In a group realizing `Q >= P`, the partition of `M` by left cosets of
   `U = <m_i^-1 m_j>` merges `k` with `l` whenever `(k, l)` lies in the `P`-class of `(i, j)` or of `(j, i)`.
   This holds because the `Q`-classes are unions of `P`-classes, and `m_k^-1 m_l` in `{q, q^-1}` lies in `U`.
4. **Finite check** (`coset.py`). For each survivor rule and each blocking `P`, search for a pair `(i, j)` such that
   every coarsening of the forced partition, except the one-block partition, satisfies one of the lemma's two
   conditions. The one-block partition means `M` lies in `U`, so `<M>` is cyclic, which is step 1's amenable case.
   - Result: all blocking partitions are killed for 89 rules, listed in `coset.json` under `killed` with the
     witness pair for each `P`.
5. **Control** (`control.py`, which shares no code with `coset.py`). Direct evaluation on `S_4`, `S_5`, `A_5`,
   `D_12`, `S_3 x S_3` and `Z_2 x S_4` (`control.out`).
   - **Lemma check.** In 143 random instances where the lemma predicts a collision, `tau(1_U)` and `tau(0)`, or the
     complements, agree at every group element.
   - **Witness check.** 59,123 random placements realize a coarsening of a killed rule's blocking partition. Of
     these, 1,529 have `M` inside `U`. In the other 57,594 the collision is confirmed by evaluation, and every one of
     the 89 rules is exercised.
   - **Scope of the control.** Finite groups never carry injective unbalanced rules. So the control tests the
     implication "`Q >= P` gives a collision or a cyclic memory" and the collision itself; it does not test
     injectivity.
