---
rg: 2
id: sl3z-admits-nonsofic-action
kind: claim
title: SL3(Z) has a p.m.p. action that is not sofic
root: true
distinct_from:
  groups-containing-kun-thom-pair-have-nonsofic-actions: that gives nonsofic actions to every group containing an infranormal non-normal Kazhdan pair; no such pair is known inside SL3(Z), and this asks whether the arithmetic lattice itself leaves Paunescu's class
  kun-thom-free-nonsofic-action: that is a nonsofic action of a non-linear elementary group over Laurent polynomials; this asks the same for the standard higher-rank lattice
---

**OPEN.** `SL_3(Z)` admits a p.m.p. action on a standard probability space that is
not sofic (Păunescu Definition 1.4). Equivalently (Păunescu Theorem 3.1),
`SL_3(Z)` is not in Păunescu's class `𝒮`, and then it has a free nonsofic action.

Why ask. `SL_3(Z)` is residually finite and Kazhdan, the prototype of the groups
Kun--Thom's mechanism needs, yet the recorded counterexamples live on
`EL_r(F_q[x_1^(±1),...,x_d^(±1)]) ⋊ SL_d(Z)`. By
`sofic-action-class-closed-under-commensurability` the answer is the same for
every finite-index subgroup of `SL_3(Z)` and every group commensurable with it.

## Attempts

* **Kun--Thom Theorem C.** Needs a Kazhdan subgroup `Γ` that is infranormal but
  not normal. A finite-index infranormal subgroup is normal (its compressions have
  the same index, so the compression semigroup is the normalizer; argument in
  `kun-thom-free-nonsofic-action-proof`, Step 0). So the attack needs an
  infinite-index Kazhdan subgroup of `SL_3(Z)` whose compression semigroup
  generates `SL_3(Z)`. None is recorded here.
* **Overgroup transfer.** `groups-containing-kun-thom-pair-have-nonsofic-actions`
  would apply if `SL_3(Z)` contained an infranormal non-normal Kazhdan pair, or if
  some subgroup of it had a nonsofic action. Neither is known.
* **Mixing actions.** Blind to the fixed-algebra mechanism for every Kazhdan
  subgroup (`kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions`), so a
  mixing candidate such as a Gaussian or algebraic action needs a different
  obstruction. Theorem 4.1 is blind to them too
  (`permutation-centralizer-blind-to-weakly-mixing-actions`). Conversely,
  `howe-moore-lattice-nonsofic-action-transfers-to-mixing` shows `SL_3(Z)` has a
  nonsofic action iff it has a free mixing one, `SL_3(R) ×_(SL_3(Z)) Z'`. So
  restricting to mixing actions loses nothing. But a mixing witness is most
  naturally proved nonsofic by orbit equivalence to a non-mixing one.
* **The lattice-space action (sofic, dead as a candidate).** The explicit free
  mixing candidate `SL_3(Z) ↷ SL_3(R)/SL_3(Z)` is sofic
  (`sl3z-lattice-space-action-is-sofic`). Its Hecke orbits are finite and
  equidistribute, and `finite-equidistributed-orbits-give-sofic-action` turns them
  into finite models. So induction through `SL_3(R)` preserves soficity in both
  directions, and a mixing witness must come from a nonsofic seed. The explicit
  candidate with no periodic orbits is
  `sl3z-on-cocompact-lattice-quotient-is-not-sofic`, with route
  `sl3z-nonsofic-action-from-cocompact-lattice-quotient`.
* **Other lattices of `SL_3(R)`.** Equivalent to this claim:
  `paunescu-class-is-measure-equivalence-invariant` shows `SL_3(Z)` has a nonsofic
  action iff some lattice of `SL_3(R)` does, e.g. a cocompact torsion-free one from
  a division algebra of degree `3`, iff some group measure equivalent to `SL_3(Z)`
  lies outside Păunescu's class. A nonsofic action of a lattice of any other
  Howe--Moore group answers only the mixing root
  (`simple-group-lattice-admits-nonsofic-action`).
* **Positive side, rank-one contrast.** Every lattice of `PSL_2(C)` lies in
  Păunescu's class (`hyperbolic-3-manifold-groups-in-paunescu-class`): a fibered
  finite cover is surface-by-`Z`, and `paunescu-class-closed-under-amenable-extensions`
  induces sofic embeddings over Følner windows of the quotient. That mechanism needs
  a normal subgroup in `𝒮` with amenable quotient. `SL_3(Z)` has none of infinite
  index (Margulis normal subgroup theorem), and its finite-index subgroups bring
  nothing new, so a proof that `SL_3(Z) ∈ 𝒮` cannot come from extensions and would
  need a genuinely higher-rank construction.
* **Containment seeds (solve-sofic-actions, 2026-09-13).** By
  `free-action-containing-nonsofic-group-relation-is-nonsofic`, one free `SL_3(Z)`-action whose
  restricted orbit relation contains a free action of any nonsofic group puts `SL_3(Z)` outside `𝒮`,
  with no subgroup inclusion needed. For the known nonsofic Kazhdan witness `K = L_(F_2)(1,2)^×`
  Bernoulli seeds are dead: `simple-kazhdan-bernoulli-relation-hosts-contain-the-group` (Popa cocycle
  superrigidity plus simplicity) would force `K <= SL_3(Z)`, impossible since `SL_3(Z)` is residually
  finite (`leavitt-unit-bernoulli-relations-have-no-sofic-host`). Still open as seeds: non-s-malleable
  free actions of `K`, and nonsofic groups that are not simple Kazhdan.
* **Seeds that are not simple Kazhdan groups (solve-sl3z-nonsofic-seed, 2026-09-13).** Two more no-gos.
  * **Bernoulli seeds.** Take a group with a wq-normal infinite Kazhdan subgroup, and a free factor of one
    of its Bernoulli shifts, over any base. Its relation inside a host forces a finite-kernel morphism into
    the host (`rigid-bernoulli-seed-relations-embed-their-group-in-the-host`). So the Kun--Thom wreaths, and
    every group containing one, give no Bernoulli seed for any sofic host.
  * **Kun--Thom relations.** The nonsofic generalized Bernoulli relations of Theorem E pairs over `F_q` sit
    in no free action of a group without infinite elementary abelian `p`-subgroups
    (`kun-thom-actions-have-no-host-without-p-torsion`), and `SL_3(Z)` is such a group.
  * **What survives.** Free actions of nonsofic groups that are neither Bernoulli factors nor generalized
    Bernoulli over `G/Γ ⊔ G`: algebraic, Gaussian, homogeneous or co-induced actions, and products
    `Bernoulli × τ`, where Popa's Theorem 0.1 untwists only to a cocycle of `τ`. Also nonsofic groups in which
    no nonsofic subgroup is known to have a wq-normal infinite Kazhdan subgroup. Dies at: no non-malleable
    free action of a nonsofic group is recorded.
* **Product seeds and hosts with p-torsion (solve-sl3z-nonbernoulli-seed, 2026-09-13).** Two more no-gos.
  * **Products `Bernoulli × τ`.** For a Kazhdan seed group, containment gives finite-kernel morphisms from almost
    every stabilizer of `τ` into the host (`kazhdan-bernoulli-product-seed-stabilizers-embed-in-host`). So product
    seeds need `τ` with stabilizers that embed into `SL_3(Z)` modulo finite subgroups, and for essentially free `τ` the
    theorem says nothing.
  * **Kun--Thom relations, every linear host.** A host of a Kun--Thom relation receives a morphism from the Kun--Thom
    group that is injective on `SL_d(Z)` and on the root subgroups
    (`kun-thom-relation-hosts-contain-sl-d-z-and-root-groups`). So no group linear over any field is a host,
    including `SL_3(F_p[t])` and every `S`-arithmetic group over a function field.
  * **What survives.** Essentially free, non-malleable actions of nonsofic groups (algebraic, homogeneous or
    co-induced ones), and `Bernoulli × τ` with `τ` essentially free. No cocycle superrigidity theorem for these is
    imported, and no containment construction is recorded. Dies at: the same point, with product seeds narrowed to
    essentially free `τ`.
* **Full-group Kun--Thom pairs (sw-088, 2026-09-17).** The first bullet is stuck because no infranormal non-normal
  Kazhdan pair is recorded inside `SL_3(Z)`. So move the pair from the group into the full group `[R_a]` of a free
  action, where it acts by piecewise `SL_3(Z)` elements and need not be free, linear or ergodic.
  * `full-group-kazhdan-pairs-have-invariant-fixed-algebras` holds modulo Theorem 4.1: Theorem C holds for every
    Kazhdan infranormal pair `Γ ≤ H ≤ [R_a]` of a sofic free action. The proof uses swap permutations on a doubled
    space, which lie outside the embedded crossed product.
  * This gives the one-direction reduction `sl3z-nonsofic-from-full-group-kun-thom-violation` to the open
    measurable statement `kun-thom-violation-inside-free-sl3z-orbit-relation`.
  * **Dead seeds.** Finite `Γ`-orbits die unconditionally. Constant cocycles die, since they give back the first
    bullet. Untwistable cocycles with an ergodic infinite torsion abelian subgroup die, which kills generalized
    Bernoulli seeds of the Theorem E groups via Popa superrigidity (sketch).
  * **What survives.** Non-constant cocycles `H × X → SL_3(Z)` of non-malleable Kazhdan-pair actions; cohomologous
    but non-constant cocycles are a recorded gap. No candidate is recorded.
