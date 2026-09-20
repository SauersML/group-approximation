---
rg: 2
id: ct-z-has-an-infinite-finitely-generated-periodic-subgroup
kind: claim
title: "Kourovka 19.46 (S. Kohl): Kohl's class transposition group CT(Z) has an infinite finitely generated periodic subgroup"
distinct_from:
  ct-p-z-mixed-ray-torsion-reduces-to-sweeping-orbits: that proves the mixed-ray constraints (finite iff frozen everywhere; periodic infinite needs a sweeping orbit); this is the problem itself, as a target for routes and obstructions.
  periodic-k-graph-subgroups-with-ray-cocycle-are-finite: that settles the positive-ray regime negatively; this is the whole question.
  brin-thompson-groups-contain-infinite-periodic-groups: that is the analogous existence question for nV, whose k-graph uses the product rule; CT_P(Z) is the full group of the carry-rule k-graph.
---

**OPEN.** Kourovka Notebook, Problem 19.46 (S. Kohl), verbatim from the 21st issue's TeX
(swarm file `lanes/bh-kourovka/kblocks4.txt`): "Does the group CT(Z) have finitely
generated infinite periodic subgroups? (See the definition of CT(Z) in 17.57)."

A finitely generated subgroup of `CT(Z)` lies in some `CT_P(Z)`, `P` a finite set of odd
primes. So the claim is: for some `P`, `CT_P(Z)` has an infinite finitely generated periodic
subgroup. A positive answer through a Grigorchuk group would also answer Kourovka 17.58
(subgroups of intermediate growth) positively.

## What is known

- **Integral and tame parts.** A finitely generated group of integral rcwa permutations with
  common modulus `M` embeds in `Z ≀ Sym(M)`, so its periodic subgroups are finite.
- **Positive rays.** Periodic subgroups with slopes in `γ^Z`, `γ ≥ 2` an integer, are finite:
  `periodic-k-graph-subgroups-with-ray-cocycle-are-finite` (one-stack pumping).
- **The full-shift part.** `[[α]] ≤ CT_{3}(Z)` (Conway's amusical permutation) is torsion
  locally finite: `conway-amusical-permutation-is-the-full-three-shift` and
  `full-shift-topological-full-groups-are-torsion-locally-finite`.
- **Mixed rays.** An infinite periodic example needs an orbit whose tails sweep whole level
  segments: `ct-p-z-mixed-ray-torsion-reduces-to-sweeping-orbits`. That node was refereed PASS
  with repairs to its item-2 proof (a3b10b78df).
- **Germs (heuristic remark, not a theorem).** CT(Z) has only positive slopes, so germ groups at points of `Ẑ` are torsion-free,
  and a periodic subgroup acts with trivial germs at its fixed points.
  - Grigorchuk's and Nekrashevych's periodic groups have a noncyclic germ group at their
    singular point (Klein four for Grigorchuk's first group). So they can only enter CT(Z)
    with that point blown up, i.e. through a factor map.
- **Single elements.** `ct-p-z-recurrent-slope-tails-force-isometric-minimal-sets`: an element
  whose restriction to a clopen invariant set has an infinite minimal subshift as a factor
  must have slope potentials that dip below every level at all scales, along every orbit, in
  both time directions.

## Routes

- `ct-z-periodic-groups-via-subshift-factors-of-elements`. One element with a Grigorchuk
  subshift factor on a clopen invariant set suffices.
