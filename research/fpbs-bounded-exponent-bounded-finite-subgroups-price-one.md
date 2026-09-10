---
rg: 2
id: fpbs-bounded-exponent-bounded-finite-subgroups-price-one
kind: claim
title: Every infinite bounded-exponent group with uniformly bounded finite subgroup orders has fixed price one
root: true
---

OPEN research target, not an established theorem. Neither the subgroup-relative-cost theorem nor the quantitative finite-subgroup bound proves cost one when finite subgroup orders are uniformly bounded and no cost-one infinite subgroup is available. Includes the still-undetermined odd Burnside upper-cost branch from the preceding note. No implication resolving the universal Fixed Price or Benjamini-Schramm goal is asserted.

## Attempts

* **Transfer cost one from an infinite subgroup.**
  `fpbs-bounded-exponent-subgroup-relative-cost` proves that every infinite
  subgroup of a bounded-exponent group has zero relative cost in every free
  action, so a single infinite subgroup of cost one gives the whole group
  fixed price one. This is exactly how the two proved corollaries work:
  Held's theorem supplies an infinite abelian subgroup in every infinite
  2-group (`fpbs-bounded-exponent-two-groups-fixed-price`), and Ivanov and
  Ivanov--Olshanskii supply infinite locally finite subgroups in the specified
  large even Burnside range (`fpbs-large-even-burnside-fixed-price`). **Where
  it dies:** Section 8.3 of
  `research/artifacts/fpbs/docs/fixed-price-bounded-exponent-progress.md`
  states it exactly. The theorem strengthens subgroup comparison but does not
  manufacture a cost-one infinite subgroup inside a group all of whose usable
  infinite subgroups have unknown cost, and under a uniform bound on the
  orders of finite subgroups there is nothing to feed it.
* **Use the quantitative large-finite-subgroup criterion.** The same note
  proves a fixed-price criterion from large finite subgroups. **Dead in this
  hypothesis:** it is vacuous precisely when finite subgroup orders are
  uniformly bounded, which is the defining assumption here.
* **Settle the odd Burnside branch and read it off.** The undetermined odd
  branch is inside this claim's scope. `fpbs-burnside-common-upper-cost` gives
  a single value `c_n` shared by `B(m,n)` and all its infinite subgroups, with
  `1<=c_n<=2-2/n`, so `fpbs-burnside-upper-cost-one` would give cost one to
  every infinite subgroup at once. **Where it dies:** `c_n` is undetermined.
  Large odd Burnside groups have cyclic finite subgroups of bounded order, so
  they are exactly the excluded case rather than a source of the missing
  subgroup, and every route to `c_n=1` listed on that node is an unconstructed
  target.
* **Collision absorption.** The improvement over the previous note is that a
  collision among torsion detours identifies a centralizer through which an
  element can be added cheaply, and first returns remove already-absorbed
  shared powers, so no hypothesis that centralizers be finite or abelian
  remains (`fpbs-finite-detour-centralizer-dichotomy`,
  `fpbs-first-return-torsion-detours`). **Where it dies:** the dichotomy
  produces a quantitatively large *commuting* subgroup, whose cost is again
  unknown when the finite subgroups are of bounded order.
