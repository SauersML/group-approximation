---
rg: 2
id: thompson-f-relator-system-stable-in-permutations
kind: claim
title: The two relators of Thompson's F are stable in permutations (Arzhantseva--Paunescu Open problem)
root: true
distinct_from:
  almost-commuting-permutations-are-near-commuting: that is the proved stability of the commutator system; this is the Thompson two-relator system, whose stability is open.
  thompson-f-is-not-sofic: that is the group-level statement; this is the finitary permutation statement Arzhantseva and Paunescu posed, equivalent to it by thompson-f-sofic-iff-relator-system-unstable.
---

**OPEN.** The system `R = {[ab^-1, a^-1ba], [ab^-1, a^-2ba^2]}` is stable in permutations with the
normalized Hamming distance (Arzhantseva--Păunescu, arXiv:1410.2626v2, Definition 3.2). Equivalently, by
`almost-commuting-permutations-are-near-commuting`, every `delta`-solution `(A, B)` in `Sym(n)` has
`d(AB, BA) < epsilon(delta)` with `epsilon(delta) -> 0` uniformly in `n`.

*Marked root: a named open problem.* Arzhantseva--Păunescu, p. 3, verbatim: "Open problem. Is the system
of two words [ab^-1, a^-1ba] and [ab^-1, a^-2ba^2] (weakly) stable in permutations?" Their "weakly"
variant (their Definition 7.1, not read) is not recorded here.

**Equivalence.** By `thompson-f-sofic-iff-relator-system-unstable` this claim holds exactly when `F` is
not sofic. It then makes `V` nonsofic too.

## Attempts

- **Exact solutions.** They all commute, since finite quotients of `F` are abelian. This is the
  finite-group shadow of the claim, and it does not reach `delta`-solutions.
- **Kazhdan compression.** No instance: `F` has the Haagerup property
  (`a-t-menable-groups-have-no-rigid-compression-defect`).
- **Uniform stability.** Fournier-Facio--Rangarajan, arXiv:2301.03970, prove uniform stability of `F`
  for submultiplicative norms. Their text says the pointwise permutation statement "would imply that F
  is not sofic", and they treat it as out of their scope.
- **Naive permutation search (2026-09-13): uninformative.** Simulated annealing with single transpositions, for
  `n` from 64 to 1024, never beat random-level relator defect while keeping `d(AB,BA) >= eps`
  (`research/artifacts/thompson-f-sofic-anneal-2026-09-13.md`). The landscape is flat for relators of length 10 and 14, so this is
  no evidence for stability. A meaningful search must start from structure (near-commuting pairs, or truncated
  dyadic-tree actions).
- **Structured starts (2026-09-13): spatial models excluded.**
  - **Method.** Exact counts replace annealing (`research/artifacts/thompson-f-spatial-permutation-models-2026-09-13.md`).
  - **Truncations.** Truncated dyadic-tree actions put their generators off the true action on a quarter of the
    points, and their relator defect stays above 0.53.
  - **Bound.** Once the generators follow an action of `F` over the interval on all but `δ` of the points,
    `d(AB,BA) ≤ 4δ + k sqrt(6δ)` (`thompson-f-spatial-permutation-models-almost-commute`).
  - **Perturbations.** Perturbing a commuting pair costs about twice its separation in defect.
  - **Reading.** Every spatial almost-solution is near-commuting. This agrees with the claim but says nothing
    beyond that class.
- **Rate form (2026-09-14): the claim is automatically linear.**
  - **Criterion.** Coordinatewise powers multiply fixed-point proportions. So this claim holds exactly
    when one constant `C` gives `d(AB,BA) ≤ C max_j d(R_j(A,B),1)` for all pairs. It fails exactly when
    the ratio of relator defect to separation has infimum 0
    (`thompson-f-sofic-iff-defect-to-separation-ratio-vanishes`). Disjoint unions and coordinatewise
    products never lower that ratio below `min(r,1)`.
  - **Constant.** Exact enumeration over `Sym(n)` for `n ≤ 12` gives a pair with
    `max(m_1,m_2)/m_c = 1/3`, so any such `C` is at least 3
    (`research/artifacts/hl-f-sofic-relator-instability-2026-09-14.md`).
  - **Proved classes.** On pairs where a fixed nontrivial element of `F` is almost trivial, the inequality
    holds with linear constants (`thompson-f-almost-kernels-force-linear-commutator-bounds`).
- **Metabelian wall and skew products (2026-09-14).**
  - **Sharp metabelian case.** `c ≡ (a^2R_1a^-2)(aR_1a^-1)(a^2R_2a^-2)^-1` modulo `F_2''`, so pairs
    generating a metabelian group satisfy `d(AB,BA) ≤ 2 d(R_1,1) + d(R_2,1)`, and the bound is attained
    (`thompson-f-metabelian-pairs-obey-sharp-linear-commutator-bound`). The `n ≤ 12` minima above are
    attained by metabelian groups and equal this bound.
  - **Every bounded derived length.** Linear constants `N_ℓ` exist for each derived length and for every
    law `F` escapes (`thompson-f-bounded-derived-length-pairs-obey-linear-bounds`). Skew products over
    commuting bases with unrestricted fibres already contain every pair, so no barrier uniform over them
    is weaker than this claim.
  - **Constant.** Annealing over `Sym(3)`-fibre skew products on `Z/3 × Z/3` gives a 27-point pair with
    `max(m_1,m_2)/m_c = 4/21`, of derived length at most 3. So any `C` is at least `21/4`, and
    `N_3 ≥ 21/4 > N_2 = 3`. Iterated skew products and larger tori gave no further gain
    (`research/artifacts/hl-f-skew-product-rate-2026-09-14.md`).
