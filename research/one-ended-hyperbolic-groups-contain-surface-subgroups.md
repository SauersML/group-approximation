---
rg: 2
id: one-ended-hyperbolic-groups-contain-surface-subgroups
kind: claim
root: true
title: Every one-ended hyperbolic group contains a surface subgroup
distinct_from:
  closed-hyperbolic-3-manifold-groups-contain-surface-subgroups: that is the Kahn--Markovic case of closed hyperbolic 3-manifold groups; this is Gromov's question for all one-ended hyperbolic groups.
  random-groups-below-density-half-contain-surface-subgroups: that holds with overwhelming probability in the density model; this asks for every one-ended hyperbolic group.
  cyclic-graphs-of-free-groups-contain-surface-subgroups: that covers graphs of free groups with cyclic edge groups; this asks for all one-ended hyperbolic groups.
  kms-hb2-groups-contain-genus-two-surface-subgroups: that covers the KMS groups G_HB2(p) for every odd prime p, including infinitely many hyperbolic Kazhdan groups; this asks for all one-ended hyperbolic groups.
---

**OPEN.** Gromov's surface subgroup question: does every one-ended hyperbolic group
contain the fundamental group of a closed surface with `chi < 0`?

## Where it is asked

- H. Wilton, arXiv:1701.02505, Question `qu: Gromov` (l.149--151), verbatim: "Does
  every one-ended hyperbolic group contain a surface subgroup?"
- D. Calegari and A. Walker, arXiv:1304.2188, l.92--95, verbatim: "Let $G$ be a
  one-ended hyperbolic group. Does $G$ contain a subgroup isomorphic to the
  fundamental group of a closed surface with $\chi<0$?". At l.105: "the Surface
  Subgroup Question is wide open in general".

## Covered classes (imports ESTABLISHED on main)

1. Closed hyperbolic 3-manifold groups:
   `closed-hyperbolic-3-manifold-groups-contain-surface-subgroups` (Kahn--Markovic).
2. Random groups at every density `D < 1/2`, and random one-relator groups:
   `random-groups-below-density-half-contain-surface-subgroups` (Calegari--Walker).
3. One-ended hyperbolic graphs of virtually free groups with virtually cyclic edge
   groups, including limit groups: `cyclic-graphs-of-free-groups-contain-surface-subgroups`
   (Wilton). Wilton also reduces the question, for groups without 2-torsion, to the
   rigid case (no splitting over a virtually cyclic group).
4. Uniform lattices in center-free complex semisimple groups, and in groups with
   the flip assumption, which includes every rank-one group except `SO(1,2n)`:
   `flip-uniform-lattices-contain-surface-subgroups` (Kahn--Labourie--Mozes).
5. Random ascending HNN extensions of free groups, and Sapir's group:
   `random-ascending-hnn-of-free-groups-contain-surface-subgroups` (Calegari--Walker).
   Most such groups are not hyperbolic, so this is evidence rather than coverage.
6. Second-hand only, not read at source: Coxeter groups (Gordon--Long--Reid);
   Hamenstädt for rank-one groups except `SO(2n,1)`.
7. Four of the six hyperbolic Kac--Moody--Steinberg families of
   Caprace--Conder--Kaluba--Witzel, `G_HB2(2)(p)`, `G_HC2(2)(p)`, `G_HB2(3)(p)` and
   `G_HBC2(3)(p)`, for every odd prime `p`. For `p >= 7` (respectively `p >= 11`) these are
   hyperbolic with property (T), so rigid. Proved here, computer-certified:
   `kms-hb2-groups-contain-genus-two-surface-subgroups`,
   `kms-hc2-hb3-hbc3-contain-genus-two-surface-subgroups`, via the criterion
   `kms-girth-surfaces-give-surface-subgroups` (and `ghb7-contains-a-genus-two-surface-subgroup`
   for `p = 7`). The families `G_HC2(1)(p)` and `G_HBC2(2)(p)` are not covered yet.

## First uncovered natural classes

1. **Uniform lattices in `SO(2n,1)`, `n >= 2`.** The flip assumption fails there
   (Kahn--Labourie--Mozes, l.197), and Hamenstädt excludes the same case.
2. **Hyperbolic free-by-cyclic groups `F_n x|_phi Z`.** The edge group is all of
   `F_n`, so Wilton's cyclic-edge theorem does not apply. By
   `automorphism-immersion-representatives-have-finite-order`, Calegari--Walker's
   immersion criterion can never apply to them either. Only their bounded-folding
   criterion remains.
   - For a rose representative, bounded folding means the factor `R_1 -> R` is an
     immersion, or its folding region is one tree at the vertex (arXiv:1212.2618,
     l.1032--1042 and l.1092--1100).
   - What is missing: a boundedly `f`-folded fatgraph for some atoroidal `phi` of
     `F_n`, `n >= 3`. In rank 2 every mapping torus contains `Z^2` or a Klein-bottle
     group, so it is not hyperbolic.
   - No theorem covering this class was found in the sources read.
3. **Rigid one-ended hyperbolic groups in general,** after Wilton's reduction.

## Scope of the literature check

Five arXiv sources were read at TeX source on MSI: 0910.5501, 1304.2188, 1212.2618,
1701.02505 and 1805.10189. Later results, for example on non-uniform lattices, on
`SO(2n,1)`, or on free-by-cyclic groups, were not searched. So "uncovered" means
uncovered in these sources, not known to be open.
