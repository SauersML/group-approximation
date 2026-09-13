---
rg: 2
id: strong-atiyah-passes-to-locally-indicable-extensions
kind: claim
title: Strong Atiyah passes from a torsion-free normal subgroup to extensions with locally indicable quotient
distinct_from:
  atiyah-passes-to-torsion-free-elementary-amenable-extensions: that is Schick's permanence for torsion-free elementary amenable quotients, proved by Ore localization; this is the Jaikin-Zapirain--Lopez-Alvarez permanence for locally indicable quotients, which covers free quotients and is proved by a complexity induction on the division closure.
  universal-torsion-free-hosts-not-sofic-or-locally-indicable: that shows a universal torsion-free host is not locally indicable, so the locally indicable theorem does not apply to the host; this is an extension theorem with an arbitrary kernel, so it still applies to subgroups of such hosts that map onto a locally indicable group with a Strong Atiyah kernel.
---

**ESTABLISHED (literature import)** by [[strong-atiyah-locally-indicable-extension-citation]].

Let `K` be a subfield of `C`, let `G_2` be a group, and let `G_1` be a
torsion-free normal subgroup of `G_2` that satisfies the Strong Atiyah
conjecture over `K`. If `G_2/G_1` is locally indicable, then `G_2` satisfies
the Strong Atiyah conjecture over `K`.

The kernel `G_1` is arbitrary. It may have property (T), and it need not be
sofic or locally indicable.

## Source

A. Jaikin-Zapirain and D. Lopez-Alvarez, *The strong Atiyah and Lueck
approximation conjectures for one-relator groups*, arXiv:1810.12135v4
(11 Nov 2019), Math. Ann. 376 (2020). Read from the arXiv PDF on 2026-09-12,
pages 5-6 and 30-35.

* **Proposition 6.5**, verbatim: "Let K be a subfield of C. Let G_2 be a group
  and G_1 a torsion-free normal subgroup of G_2 satisfying the strong Atiyah
  conjecture over K. Assume that G_2/G_1 is locally indicable. Then G_2
  satisfies the strong Atiyah conjecture over K."
* **Credit.** The paper attributes the observation to Fabian Henneke and Dawid
  Kielak (p. 31: "This was pointed out by Fabian Henneke and Dawid Kielak";
  Acknowledgments, p. 6: "our argument can be used to prove that the class of
  torsion-free groups satisfying the Atiyah conjecture is closed under
  extensions by locally indicable groups").
* **Printed proof.** Induction on the `G_2`-complexity of a nonzero `a` in the
  division closure `D_(K[G_2])` inside `R_(C[G_2])`. For an expression realizing
  that complexity, with finitely generated source subgroup `H`: "if H <= G_1,
  then a is invertible because G_1 satisfies the strong Atiyah conjecture over
  K. Otherwise HG_1/G_1, and so H, is indicable, and therefore there exists
  N ◁ H with H/N ≅ Z." Propositions 3.11 and 5.1 then give invertibility of `a`
  as in Theorem 6.1.

## Trust surface

* Read: the statement and printed proof of Proposition 6.5, the statement and
  proof of Theorem 6.1, and Corollaries 6.2-6.3.
* Not re-derived: Proposition 3.11, which says the von Neumann rank is
  Hughes-free, and Proposition 5.1, the Laurent-series step of the induction.

## Model test

* **Recovers the base case.** `G_1 = 1` gives Theorem 1.1 of the same paper:
  locally indicable groups satisfy Strong Atiyah over `C`.
* **The quotient hypothesis cannot be dropped.** Take `G_1 = Z` inside the
  infinite dihedral group `G_2 = Z semidirect Z/2`. The kernel is torsion-free
  and satisfies Strong Atiyah, but the quotient `Z/2` is not locally indicable,
  and `(1 + s)/2`, for `s` a reflection, is a projection of trace `1/2`.
* **A real object with a Kazhdan kernel.** Let `Gamma(3) <= SL_3(Z)` be the
  principal congruence subgroup and let a free group `F` act on it by
  conjugation through any homomorphism `F -> SL_3(Z)`. `Gamma(3)` satisfies
  Strong Atiyah over `C` (`congruence-kazhdan-groups-satisfy-strong-atiyah`) and
  has property (T). So `Gamma(3) semidirect F` satisfies Strong Atiyah over `C`,
  even though it is neither locally indicable nor in Linnell's class.

## Uses in this graph

* `double-ascending-hnn-strong-atiyah-reduces-to-kernel-tree` removes the free
  quotient of a multiple ascending HNN extension. What remains is the amalgams
  over compressed copies of the base.
* At the universal host, `universal-torsion-free-hosts-not-sofic-or-locally-indicable`
  kills the locally indicable theorem. The relative form here is not killed: it
  applies to any subgroup that maps onto a locally indicable group with a kernel
  already known to satisfy Strong Atiyah.
