---
rg: 2
id: stw18-k1-witness-strict-comparison-not-k1-injective
kind: claim
title: A simple separable unital nuclear algebra with strict comparison is not K1-injective
distinct_from:
  stw18-strict-comparison-non-z-stable-algebra-exists: that asks only for failure of Z-stability; this asks for the sharper, checkable certificate of a unit-level K1 obstruction, which implies it through Jiang's theorem.
  stw59-simple-ah-non-k1-injective: that constructs a simple unital AH algebra that is not K1-injective with no comparison property, and it necessarily fails strict comparison; this demands strict comparison as well.
  stw99-problem-lix-simple-k1-injective: that universal question on simple algebras is already refuted; this asks for the refutation inside the strict-comparison class.
artifacts:
  - research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md
---

**OPEN.** There is a simple, separable, unital, nuclear, non-elementary
C*-algebra `A` with strict comparison of positive elements, with respect to a
nonempty trace simplex, and a unitary `u in U(A)` with `[u] = 0` in `K_1(A)`
but `u` not in `U_0(A)`.

Such an `A` is a counterexample to both Problem XVIII and Problem XXIII; see
`stw18-k1-witness-constraints` for everything it is forced to satisfy.

## Attempts

- **Strict-comparison upgrade of the LIX towers.** Dead:
  `simple-ah-strict-comparison-is-k1-injective`. Every such upgrade with
  homogeneous building blocks is AH, and Toms plus Jiang make AH algebras
  with strict comparison K1-injective. The existing LIX algebras fail strict
  comparison (`stw59-lix-algebras-fail-strict-comparison`).
- **Where the topology must go in any type I tower.**
  `homogeneous-tower-k1-failure-needs-twice-rank-dimension`: at every late
  stage some block has spectrum dimension at least twice its rank.
  `untwisted-point-evaluations-kill-k1-obstructions`: pullback plus untwisted
  point-evaluation connecting maps kill the obstruction in one step. So the
  complement added by the connecting maps must be topologically twisted; in
  the LIX towers it carries half the trace with nonvanishing `c_1(L)^(r_j)`,
  which is Villadsen's perforation. These are necessary conditions, not a
  no-go outside AH.
- **Non-type-I exclusions (2026-09-12).** Free minimal crossed products
  `C(X) ⋊ Gamma` are closed on both counts. With (URP) and (COS), in particular
  every `C(X) ⋊ Z^d`, they have stable rank one
  (`urp-cos-crossed-products-are-k1-bijective`). With (URP) alone they satisfy
  Toms--Winter (`urp-crossed-products-satisfy-toms-winter`). Every building
  block of any presentation must fail K1-injectivity at a tail
  (`unital-limits-of-k1-injective-algebras-are-k1-injective`). So Z-stable,
  stable-rank-one, purely infinite and URP crossed-product blocks are all
  useless.
- **Surviving design space.** A witness must be non-AH (for example
  approximately subhomogeneous with nonhomogeneous blocks, or built from
  non-type-I blocks), have stable rank at least two, an unrealized rank
  function (so it refutes the Rank Problem), no pureness, and a trace simplex
  outside every condition (C) stratum. No candidate is known; the XXIII root
  records that no candidate for failure of the Rank Problem is known either.
