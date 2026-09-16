---
rg: 2
id: soluble-automatic-groups-are-polycyclic
kind: claim
title: Every soluble automatic group is polycyclic
distinct_from:
  polycyclic-automatic-groups-are-virtually-abelian: that assumes polycyclic and concludes virtually abelian; this assumes only soluble and concludes polycyclic, the step Harkins' theorem needs as input
---

**OPEN.** If `G` is a finitely generated soluble automatic group, then `G` is polycyclic.
Equivalently, by Mal'cev's theorem that soluble groups with the maximal condition on
abelian subgroups are polycyclic (as quoted by Romankov, arXiv:1511.00223v1, §6),
every abelian subgroup of a soluble automatic group is finitely generated.

With `polycyclic-automatic-groups-are-virtually-abelian` it is equivalent to
`soluble-automatic-groups-are-virtually-abelian` (routes
`soluble-automatic-va-via-polycyclic-case` and
`soluble-automatic-polycyclic-from-virtually-abelian-case`). So it isolates exactly the
step of the biautomatic proof that has no automatic analogue.

## Attempts

- 2026-09-16 (lane swarm-amenable-automatic-groups-are-): **what a counterexample looks
  like.** The artifact `research/artifacts/amenable-automatic-groups-are-virtually-abelian-2026-09-16.md`,
  Section 7, steps R1–R3, gives the following, with Kropholler, Kargapolov and
  Robinson–Zaĭcev taken from Romankov's quotations, unread. A counterexample `G` has a
  torsion-free finite-index subgroup `H` of finite cohomological dimension that is
  automatic, soluble minimax and not polycyclic, and nilpotent-by-(virtually abelian).
  So `H` has a non-finitely-generated abelian subgroup, the model case being `Z[1/p]` as
  in `BS(1,p)`.
- **Biautomatic mechanism unavailable.** For biautomatic groups Romankov gets
  polycyclicity from the minimal condition on centralizers and Gersten–Short. This lane
  knows no analogue for automatic groups.
- **Dehn function.** `BS(1,p)` itself is excluded because its Dehn function is
  exponential (Rees, arXiv:2205.14911v1, pp. 11–12). The general case cannot be done this
  way without more input. De Cornulier–Tessera (arXiv:1003.0148, abstract read
  2026-09-16) embed `BS(1,n)` in finitely presented metabelian groups with quadratic
  Dehn function. The paper was not read, so it is unknown whether any of those groups
  are of type `FP_∞`. If one is, the Dehn function alone cannot prove this claim.
- **Distortion.** A non-finitely-generated abelian subgroup in the metabelian model
  cases comes with exponentially distorted cyclic subgroups. Undistorted cyclic
  subgroups are known to this lane only for biautomatic groups (Gersten–Short, from
  memory). Not attempted further.
