---
rg: 2
id: toms-schubert-algebra-misses-a-rank
kind: claim
title: Toms's simple AH algebra without uniform property Gamma has a continuous strictly positive affine function that is not a rank
distinct_from:
  stw23-rank-problem-counterexample-exists: that asks for any unital simple separable stably finite non-elementary algebra with an unrealized rank; this names one concrete algebra on which every known positive method is inapplicable.
  toms-ah-counterexample-to-uniform-gamma: that imports Toms's algebra and its failure of uniform property Gamma; this asks whether the same algebra refutes the Rank Problem.
  doubling-ah-finite-stage-continuous-ranks-are-constant: that is an established firewall excluding orthogonal-sum constructions of non-constant continuous ranks; this is the open question whether any construction at all realizes them.
---

**OPEN.** Let `B` be Toms's simple AH algebra without uniform property Gamma
(arXiv:2606.12188v2, `prop:sparse-simplefication-survival` and
`thm:simple-point-evaluation-no-gamma`; the adjectives are imported in
`toms-ah-counterexample-to-uniform-gamma`). Some strictly positive continuous
affine function `f` on `T(B)` is not `d(a)` for any `a in (B tensor K)_+`.

By `all-ranks-occur-iff-continuous-ranks-are-dense` this is the same as
failure of the Rank Problem for `B`, and the same as failure of uniform density
of continuous ranks on `T(B)`.

## Attempts

- **Why this algebra.** Each known positive cell of STW XXIII fails for `B`.
  - *Stable rank one* (Thiel): Toms's introduction says "the examples
    constructed here necessarily have stable rank strictly greater than one",
    because Vaccaro's theorem gives uniform Gamma to simple unital
    non-elementary AH algebras of stable rank one.
  - *Finitely many extreme traces* (Tikuisis--Toms): `T(B)` is the Poulsen
    simplex (`toms-doubling-ah-trace-simplex-is-poulsen`).
  - *Z-stability* (Elliott--Robert--Santiago): Z-stable algebras have uniform
    Gamma, which `B` lacks.
  - *Dadarlat--Toms*: needs strict comparison and a compact
    finite-dimensional boundary. `B` has neither
    (`toms-gamma-counterexample-fails-strict-comparison`).
  - *Skew products* (`stw23-skew-product-diffuse-fibres-have-all-ranks`):
    `B` is not presented that way, and the diffuse-independence input is
    unavailable (below).

  STW, arXiv:2506.10902v2, in the text before Problem XXVII, place the
  first-type Villadsen algebras under Thiel and the second type under unique
  trace. So in STW's catalogue and in this graph, `B` is the first algebra on
  which the Rank Problem is untested by every known method. This check covered
  STW's discussion, Asadi-Vasfi--Thiel--Vilalta arXiv:2310.00663 (soft
  representatives of ranks under the Global Glimm Property, which realizes no
  new rank) and one web search on 2026-09-12. It is not a full survey.
- **Known.** Rank density holds (`ah-algebras-realize-ranks-approximately`).
  So only the passage from approximate to exact realization is at stake.
- **Dead: orthogonal sums of finite-stage pieces.** By
  `doubling-ah-finite-stage-continuous-ranks-are-constant`, every continuous
  rank of that form is constant in `B`. This rules out projection sums,
  layer-cake sums and Edwards-increment sums. A realizing element for a
  non-constant `f` must be a Cuntz supremum of finite-stage elements whose
  increments are not orthogonal summands.
- **Dead: Lin's theorem.** Strict comparison plus surjective rank map forces
  stable rank one. `B` has no strict comparison, so neither direction bites.
- **Dead: Thiel's infimum method.** Thiel's proof for stable rank one has four
  steps: realize chisels (all simple algebras), realize functional infima
  (needs (O6+)), approximate from above, and take the maximal soft element
  `alpha(f) = sup L'_f`. In `B` the third conclusion is free, because the
  Brown--Perera--Toms elements approximate from above. The fourth step is
  provably unavailable: `toms-schubert-algebra-has-no-small-joins` shows that
  two compact classes of constant rank `t` in `B` have no common Cuntz upper bound
  of rank below `2(1 - eta) t` everywhere. So `L'_f` is not upward directed for
  `f = (5/4) t`, and `Cu(B)` fails (O6+) or weak cancellation.
  - The second step fails too, and the disjunction resolves.
    `toms-schubert-algebra-fails-o6-plus` is the dual statement for meets. For
    large `m`, every common Cuntz lower bound `c` of `p_m` and `q̂_m` has
    `sup_tau (d_tau(p_m) - tau(h_(2 eps)(c))) >= delta^2/8`.
  - So no common lower bound has a continuous rank near `d(p_m)`, and the
    conclusion of Thiel's Theorem 7.5 fails for this pair.
  - Hence `Cu(B)` fails (O6+) outright, and `B tensor K` is not of almost stable
    rank one.
  - Both constant targets are ranks, so neither result decides this claim. What
    they give is a two-sided rigidity of Cuntz meets and joins of Toms's twisted
    equal-rank pair.
- **The exact cell `B` escapes.** `rank-density-and-small-joins-give-all-ranks`:
  rank density plus upward directedness of every `L'_f` gives all ranks, with no
  (O6+), weak cancellation or comparison. `B` has rank density and fails
  directedness. So a realizer of a non-constant affine function in `B` has two
  constraints:
  - it is not a countable orthogonal sum of finite-stage pieces;
  - it is not the maximal soft class below its rank, since no such class exists
    for small constant targets.
  What survives is a Cuntz supremum that selects among incompatible upper bounds
  coherently across the Poulsen simplex.
- **Open positive mechanism: central diffuse independence.** Suppose that for
  a uniformly dense family of stage-central `0 <= c <= 1`, some positive
  contraction `b` commutes with `c` and has joint law `mu_(c,tau)` times
  Lebesgue for every trace. Then `d((b - (1-c))_+) = tau(c)` exactly and
  continuously, and all ranks occur. This is the abstract core of the
  skew-product theorem, and it needs independence only from the centre of a
  stage, not the uniform Gamma that Toms excludes.
  - In `B`, a finite-stage `b` fails by the firewall.
  - A limit `b` refined across twisted leaf summands has offsets that are
    functions of the leaf path, and so are the values of `c`.
  - Heuristic only: free leaf labels should allow branch traces on which
    offsets and values coincide, leaving atoms of mass about `1/r_N`.
  - Not settled either way.
- **Open negative mechanism.**
  - Take a Cuntz-increasing sequence of finite-stage elements whose ranks
    increase uniformly to a non-constant `f`. Its stage rank functions must
    jump across walls in `X_M`.
  - The normalized slack tends to `0`, while `dim X_M / r_M^2` stays of order
    one (exactly `2` for Toms's non-simple presentation).
  - Subequivalences of soft supports across walls between line-bundle-twisted
    leaf summands are where Toms's Thom--Porteous classes live.
  - A refutation needs a degeneracy class that forces rank above `f`
    somewhere and survives the supremum. None has been found.
  - **Heuristic constraint: local swaps dilute.**
    - Moving `M` directions between the two twisted halves at level `r` over
      `CP^(j_r)`, `j_r = 2 d_r^2`, is a map
      `theta^M tensor gamma_(r,1) -> theta^M tensor gamma_(r,2)`.
    - Its Hom bundle `O(1)^(M^2)` is globally generated, so a generic map has
      empty degeneracy locus `D_(s+1)` once `(s+1)^2 > j_r`. Such a swap is forced
      to degenerate only in kernel dimension up to about `sqrt(2) d_r`.
    - At stage `N >= r` the normalized cost is at most `sqrt(2) d_r / d_N`, which
      tends to `0`. A realizer can defer local swaps to deep stages.
    - So a refutation should extract a full-scale forced pair, such as
      `(p_N, q_N)`, from a realizer's approximants. This is how
      `toms-schubert-algebra-has-no-small-joins` and
      `toms-schubert-algebra-fails-o6-plus` handle joins and meets.
    - Not proved: range bundles of approximants may carry further Chern classes
      that this count ignores.
