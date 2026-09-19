---
rg: 2
id: elek-szabo-envelope-loses-torsion-free-kazhdan-control
kind: claim
title: The Elek--Szabo simple sofic envelope loses torsion-free and Kazhdan control
distinct_from:
  simple-sofic-total-mf-radical: That extracts a countable simple sofic full-MF-radical subgroup using a torsion witness; this proves why the ambient envelope and countable descent cannot provide the torsion-free Kazhdan kernel required here.
  torsion-free-lef-kazhdan-non-rf-seed: That supplies a torsion-free sofic Kazhdan input group; this shows that placing it in the Elek--Szabo envelope preserves neither torsion-freeness nor property (T) of the envelope.
  titz-witzel-simple-kazhdan-cat0-lattices-exist: Those simple Kazhdan groups are torsion-free but have unknown soficity; this concerns the complementary simple sofic construction and its missing geometric properties.
artifacts:
  - GroupApproximation/Sofic/SimpleSoficEnvelopeUnconditional.lean
  - research/artifacts/torsion-free-exact-radical-team-audit-2026-08-26.md
---

Let `S(tau/omega)` be the universal sofic group of Elek--Szabo.  Then

```text
S(tau/omega) is simple and sofic,
S(tau/omega) contains a nontrivial involution,
S(tau/omega) is uncountable and does not have property (T).       (ESK1)
```

Nevertheless it contains every countable sofic group, including the
torsion-free Kida--Thom Kazhdan seed, and every nontrivial conjugacy class
boundedly normally generates the ambient group, with a bound depending on
the class.  Thus none of the following data implies property `(T)` or
torsion-freeness of the ambient simple group:

```text
a torsion-free property-(T) subgroup,
relative property (T) for the pair,
simple soficity,
bounded normal generation by every nontrivial conjugacy class.   (ESK2)
```

The countable simple descent used by `simple-sofic-total-mf-radical` adjoins
chosen conjugators but supplies no order control, finite generating set or
Kazhdan pair.  Starting the descent from the torsion-free Kazhdan seed does
not prove that the intermediate simple group is torsion-free or Kazhdan.
Starting from the existing non-MF witness does prove full MF radical, but
injectively imports its Clifford involution; the machine-checked envelope has
no nontrivial torsion-free image.

Hence the Elek--Szabo construction does not fill the seed required by
`torsion-free-sofic-exact-mf-radical-over-z`.  A positive use would require a
new torsion-free Kazhdan simple-sofic envelope theorem which also preserves a
nonzero MF-invisible mark.
