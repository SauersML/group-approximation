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

## Attempts

- **Legal f-folded certificates for hyperbolic free-by-cyclic groups** (2026-09-17). This
  attacks uncovered class 2.
  - Criterion: `legal-f-folded-fatgraphs-give-surface-subgroups` replaces the immersion hypothesis
    by train-track legality.
  - Certificates: `hyperbolic-f3-by-z-with-genus-two-surface-certificates` gives two explicit
    automorphisms of `F_3`, whose hyperbolic mapping tori contain genus-2 surface groups.
  - Family: `hyperbolic-f3-by-z-family-with-genus-two-surfaces` gives infinitely many
    non-isomorphic hyperbolic `F_3 x| Z`, all with genus-2 surface subgroups.
  - Census: `legal-folded-certificates-at-power-one-census` shows that at power 1 the criterion is
    exactly silent on 6372 of 6420 short positive automorphisms and certifies the other 48.
  - Every rank: `hyperbolic-fn-by-z-genus-two-surfaces-every-fibre-rank` feeds a chain of new
    letters into `phi(a) = a^7 c^9 d_1 b` and reuses one certificate unchanged. The
    characteristic polynomial is `t^k (t^3 - 7t^2 - 13t - 7) - (t + 1)`, and Rouché shows it is
    Pisot, so irreducible, for every `k`. So for every `n >= 4` there is a one-ended hyperbolic
    `F_n x| Z` with a genus-2 surface subgroup, proved for all `n` at once.
  - Power two: `power-two-legal-folded-certificates-reach-beyond-power-one` shows that
    `a -> abb, b -> caaa, c -> babb` has no certificate at power 1 (exact Farkas) but a genus-5
    certificate at power 2. Its torsion in `H_1` has order 8, so this group is new. The power-2 LP
    has been run on 53 of the 444 infeasible class representatives: 44 are `infeasible-exact`, and
    7 are LP-negative, of which only entry 300 is certified so far.
  - Power-two family: `power-two-folded-fatgraphs-of-genus-k-plus-two-family`
    treats `phi_k : a -> abb, b -> c a^k, c -> babb`. For every `k >= 1` it gives a closed-form legal
    `f^2`-folded fatgraph, of genus `k + 2`, checked for all `k` by exact affine arithmetic and
    numerically for `k <= 200`. Power one is exactly silent for `2 <= k <= 30`. So infinitely many
    pairwise non-isomorphic hyperbolic `F_3 x| Z` with no power-one certificate contain surface
    groups, with certificates of unbounded size.
  - Power-two census: `power-two-word-free-census-of-power-one-silent-classes` runs the power-2 LP on
    all 444 representatives. 411 have an exact Farkas obstruction, 9 are infeasible only in
    floating point, and 24 are LP-negative. Seven are certified, giving surfaces of genus 3 to 5.
    Five of these certificates are new, among them the first certified hyperbolic `F_3 x| Z` whose `H_1` torsion
    has order 2 (`a -> ab, b -> babc, c -> bab`, genus 3). 17 LP-negative entries have no
    certificate with `|w| <= 4`.
  - Status: class 2 is now covered by explicit groups in every fibre rank `n >= 3`, not for all
    automorphisms. Raising the power strictly enlarges what the criterion certifies, and
    certificates can be proved in closed form for parametrised families. Powers 1 and 2 together
    are still exactly silent on 411 of the 535 census classes. Open: the remaining 17 LP-negative
    and 9 float-infeasible entries at `m = 2`, and a uniform argument that some power works for
    every atoroidal automorphism.
