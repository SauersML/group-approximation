---
rg: 2
id: deligne-parameter-group-is-a-virtual-invariant
kind: claim
title: Deligne's norm-parameter group is unchanged on finite-index subgroups, and the Maslov class is virtually divisible by exactly two
distinct_from:
  deligne-sep7-norm-parameter-closed-subgroup: that proves P_op is a closed subgroup containing 1/2 on Sp_4(Z) itself; this proves P_op is the same on every finite-index subgroup and computes how it transforms under virtual division of the class, reproving 1/2 in P_op from a trivial model.
  deligne-flexible-subgroup-restrictions-carry-exact-sector-models: that builds exact models on infinite-index flexible subgroups and shows finite-index subgroups are rigid; this shows finite-index subgroups contribute no new parameters at all, and that block-monomial models can only come from finite-index subgroups.
  rf-actions-induce-from-finite-index-subgroups: that induces residually finite actions from finite-index subgroups; this induces operator-norm projective quasi-representations with a fixed scalar cocycle and tracks the defect blockwise.
  metaplectic-half-class-has-an-exact-finite-model: that exhibits exact finite models at the half parameter and is used here as an input; this recovers the half parameter as the image of the zero parameter under virtual division by two, and proves no virtual division by any other integer exists.
  sp4-deligne-rigid-infinite-index-subgroup-exists: that asks for rigidity on an infinite-index subgroup; this is a statement about finite-index subgroups only.
  deligne-finite-parameter-group-has-period-prime-to-three: that is the open arithmetic hole; this proves the virtual-descent invariants under which that hole is invisible, so it does not decide it.
---

**ESTABLISHED** (route `deligne-parameter-group-is-a-virtual-invariant-proof`).

**Setting.** `Gamma = Sp_4(Z)`. `b` is the normalized integral cocycle of the universal-cover extension, as in
`deligne-sep7-norm-parameter-closed-subgroup`. For a finitely generated group `L` and a normalized integral 2-cocycle
`beta` on `L`, let `P(L, beta)` be the set of `theta in R/Z` admitting operator-norm asymptotic
`exp(2 pi i theta beta)`-models. These are maps `U_n : L -> U(d_n)` with `U_n(e) = I` and
`||U_n(g)U_n(h) - exp(2 pi i theta beta(g,h)) U_n(gh)|| -> 0` for every fixed pair. So `P_op = P(Gamma, b)`.
`P(L, beta)` depends only on `[beta] in H^2(L;Z)` (item V0 of the route).

- **(V1) Finite-index invariance.** For every finite-index `Gamma' <= Gamma`,

  ```text
  P(Gamma', b|Gamma') = P_op.
  ```

  Restriction gives `P_op <= P(Gamma', b|Gamma')`. Twisted induction gives the reverse inclusion: it turns a
  model on `Gamma'` into a model on `Gamma` whose defect at each pair `(g,k)` is the maximum of the `Gamma'`-defects
  at `[Gamma:Gamma']` pairs.
- **(V2) Division rule.** If `[b|Gamma'] = n[beta] + tau` in `H^2(Gamma';Z)`, with `n in Z` and `tau` torsion, then

  ```text
  P_op = { theta : n theta in P(Gamma', beta) },    and hence    P(Gamma', beta) = n P_op  when n != 0.
  ```

- **(V3) The virtual divisibility index is exactly two.**
  - There is a finite-index `Gamma' <= Gamma` and a class `beta` with `[b|Gamma'] = 2[beta]`.
  - For no finite-index `Gamma'` is `[b|Gamma']` in `n H^2(Gamma';Z) + Tors` with `n` not in `{1,-1,2,-2}`. This
    includes `n = 0`: `[b|Gamma']` is never torsion.

  The inputs are:
  - for attainment, residual finiteness of `E_2` (`metaplectic-half-class-has-an-exact-finite-model`);
  - for exclusion, the inclusion `<z_q^2> <= Res_fin(E_q)` of Deligne's theorem
    `deligne-covers-of-sp2g-z-have-finite-residual-2z` at `q = 3`, at `q = 4` and at odd primes.
- **(V4) Normal form.** On the `Gamma'` of (V3), `P(Gamma', beta) = 2 P_op`. The trivial model gives
  `0 in P(Gamma', beta)`, which reproves `1/2 in P_op`. On the finite branch `P_op = (1/m)Z/Z`, we get
  `P(Gamma', beta) = (1/(m/2))Z/Z`. The flagship goal `1/3 notin P_op` is equivalent to `1/3 notin P(Gamma', beta)`.
- **(V5) Virtual descent is closed on subgroups containing 1/2.** Let `Q <= R/Z` be any subgroup containing `1/2`.
  Then `Q` is closed under the following operations, each of which turns known models into new ones:
  - (a) tensor products, adjoints, direct sums and amplifications (`theta, theta' -> theta + theta', -theta, theta`);
  - (b) rephasing by coboundaries, and pullback by automorphisms `alpha` of `Gamma` with `alpha^*[b] = +-[b]`
    modulo torsion (`theta -> +-theta`);
  - (c) *virtual descent.* Pick a finite-index `Gamma'` and a decomposition `[b|Gamma'] = n[beta] + tau`. Restrict
    known `b`-models at parameters in `Q` to `Gamma'`, where they become `beta`-models at parameters in `nQ`, and
    combine these by (a). Then induce every `theta` with `n theta` in `nQ` back to `Gamma` by (V1) and (V2). This
    produces `Q + (1/n)Z/Z`.

  Iterating over finite-index subgroups of finite-index subgroups adds nothing, since they have finite index in
  `Gamma`. In particular, if `P_op = (1/6)Z/Z` then every such operation stays inside `(1/6)Z/Z`.
- **(V6) Block-monomial models come from finite `Gamma`-sets.** Let `F` be finite. Let `V : Gamma -> U(C^r (x) C^d)`
  take block-monomial values `V(g) = sum_j E_(sigma(g) j, j) (x) W_j(g)`, with each `sigma(g)` a permutation and
  each `W_j(g)` unitary. Suppose the `c_theta`-defect of `V` is below `sqrt 2` on a finite window `W_F`, depending
  only on `F` and a fixed finite presentation. Then `sigma|_F` is the restriction of a genuine action of `Gamma` on
  `{1,...,r}`. So every point stabilizer of the block pattern has finite index, and cosets of an infinite-index
  subgroup can never index the blocks.

**Class killed (obstruction to the arithmetic hole).** Consider arguments for
`deligne-finite-parameter-group-has-period-prime-to-three` that start from a `1/3`-model and produce new parameters
only by operations (a) to (c), and by topological closure. None can reach any parameter outside `(1/6)Z/Z`.
- *Invariant:* the set of virtual divisibilities `n` of the Maslov class, meaning those with
  `[b|Gamma'] in n H^2(Gamma';Z) + Tors` for some finite-index `Gamma'`. By (V3) this set is `{+-1, +-2}`.
- *Where every member dies:* the division step (c) with `3 | n`. To get `1/9` from `1/3`, or `1/3` from `0`, one
  needs a finite-index subgroup on which the class is divisible by three modulo torsion. By (V3) no such subgroup
  exists, and the reason is exactly Deligne's non-residual-finiteness of `E_3`.
- By (V6), block-monomial or permutation-twisted constructions have an honest finite `Gamma`-set as their pattern.
  The only thing they add over (c) is that the finite-index stabilizers may change along the sequence, with index
  going to infinity. That case is **not** covered by (V5), and it is the remaining algebraic loophole.

A proof of the hole therefore needs a non-algebraic input about operator-norm approximation, such as an analytic
estimate or a stability theorem, beyond finite-index manipulations.

**What this changes.**
- All finite-index subgroups carry the same parameter information as `Gamma`. The finite branch `P_op = (1/m)Z/Z`
  is consistent with every finite-index restriction, induction and divisibility relation.
- Whether `3 | m` is not visible to the virtual cohomology of `b`. That cohomology sees only the factor `2`, which
  is compatible with both `m = 2` and `m = 6`.

DERIVATION
deligne-parameter-group-is-a-virtual-invariant-proof
