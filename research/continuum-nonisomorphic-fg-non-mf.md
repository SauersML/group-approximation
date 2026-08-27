---
rg: 2
id: continuum-nonisomorphic-fg-non-mf
kind: claim
title: Continuum many non-isomorphic finitely generated non-MF groups
distinct_from:
  continuum-nonisomorphic-non-mf-cylinder: That claim requires the continuum-sized family to lie inside the literal eight-generator clopen cylinder, whose members are exactly the marked quotients of E; the witnesses here are direct products E x N_i, which enlarge E rather than quotient it, so they are not in the cylinder.
  scaling-family-pairwise-nonisomorphic: That distinguishes the explicit countable scaling family E_m, whose members are all built by the same construction at different scales; this separates isomorphism types using external direct factors and says nothing about the E_m.
  scaling-family-non-mf: That establishes non-MF for every member of the scaling family without distinguishing any isomorphism types.
  clopen-non-mf-cylinder: That is a topological statement about a nonempty clopen set of marked groups; this is a cardinality statement about abstract isomorphism types.
artifacts:
  - notes/NON_MF_ARCHAEOLOGY.md
  - GroupApproximation/Sofic/ProductMultiplicity.lean
  - GroupApproximation/Sofic/ProductMultiplicityRank.lean
  - GroupApproximation/Algebra/TorsionFreeRank.lean
  - GroupApproximation/Sofic/ContinuumMultiplicity.lean
  - GroupApproximation/Monsters/NeumannContinuum.lean
---

Two multiplicity statements:

1. The groups `E x Z^k`, `k in N`, are pairwise non-isomorphic, finitely
   presented, and non-MF.
2. There exist `2^(aleph_0)` pairwise non-isomorphic finitely generated non-MF
   groups.

## Provenance — recovered from a deleted manuscript subsection

This was a proved corollary of `non_mf_groups_exist.tex` (`\subsection{Multiplicity}`,
`cor:continuum`) that was **deleted** on 2026-08-13 by commits `8d40b3ed`
("Tighten non-MF manuscript exposition") and `4a210700`. It is recoverable in
full with

```text
git show c3501887:non_mf_groups_exist.tex    # lines 2083-2129
```

The deletion was expository, not a retraction: the same commits removed the
whole multiplicity subsection while the lemma the proof depends on
(`lem:subgroupMF`, subgroup heredity of MF) remains in the live manuscript at
line 1907 and is Lean-verified as `GroupApproximation.IsOperatorMF.subgroup`.
`notes/NON_MF_ARCHAEOLOGY.md:402` still lists "B. H. Neumann's continuum family
/ Continuum many non-isomorphic finitely generated examples" as a consequence
of the main theorem.

## Relation to the two open multiplicity questions

Both open multiplicity holes ask for something this claim does not give, and
the gap in each case is precise.

- `continuum-nonisomorphic-non-mf-cylinder` needs the witnesses inside the
  cylinder. The cylinder consists of quotients of `F_8` satisfying every
  relator of `R` with `w != 1`, i.e. exactly the marked quotients of `E`; the
  witnesses `E x N_i` are extensions of `E`, not quotients. Closing that hole
  needs continuum many pairwise non-isomorphic *quotients* of `E`, which no
  corpus argument supplies.
- `scaling-family-pairwise-nonisomorphic` needs the explicit `E_m` separated
  from each other. Part 1 here separates `E x Z^k` by the torsion-free rank of
  the abelianization, an isomorphism invariant that is cheap to compute and
  that the corpus has never tried on the `E_m`. That is the obvious first
  attempt on that hole and it is currently unattempted.
