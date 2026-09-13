---
rg: 2
id: r-fibre-w-star-bundles-divide-the-unit-uniformly
kind: claim
title: Every hyperfinite W*-bundle divides its unit uniformly by order zero matrix maps, central or not
distinct_from:
  nontrivial-w-star-bundle-with-r-fibres-exists: that asks for a bundle that is not trivial; this asks only whether every bundle carries uniformly large non-central order zero copies of every M_N, which triviality implies but which could hold in a nontrivial bundle.
  r-fibre-bundle-triviality-iff-uniform-central-halving: that is Ozawa's criterion, approximately central halving projections; this drops centrality entirely.
  trivial-r-fibre-bundles-compare-equal-trace-projections: that is a comparison property of trivial bundles; this is an existence property of arbitrary bundles.
  strict-comparison-forces-tracially-divisible-unit: that asks for divisibility of the unit of a C*-algebra with strict comparison; this asks for it in every abstract hyperfinite W*-bundle with no C*-algebra and no comparison.
artifacts:
  - research/artifacts/ex-toms-winter-bauer-divisible-unit-2026-09-12.md
---

**OPEN.** Let `M` be a strictly separable continuous W*-bundle over a compact
metrizable space `K`, with conditional expectation `E: M → C(K)` and every fibre
isomorphic to `R`. Then for every `N` and `ε > 0` there is a c.p.c. order zero map
`φ: M_N → M` with `‖E(1 − φ(1))‖ < ε`. Equivalently, the reduced power `M^U` contains
a unital copy of every `M_N`.

**Why it matters.** Applied to the strict closure of a unital simple separable
nuclear algebra `A` with Bauer trace simplex, it makes the unit of `A` tracially
divisible. So it gives `toms-winter-holds-on-bauer-tlfnd-locus` through route
`toms-winter-bauer-tlfnd-via-bundle-halving`, with no comparison input beyond strict
comparison itself. Its negation over some base gives a nontrivial bundle, answering
BBSTWW Question 3.14 (`nontrivial-w-star-bundle-with-r-fibres-exists`), certified by
an existence gap rather than a comparison gap.

**All continuous profiles follow.** The central step-function construction of
`bauer-tracially-divisible-unit-gives-bounded-rank-density` works verbatim inside `M`,
with `C(K) ⊂ Z(M)`. So the claim implies near projections of every continuous trace
profile in `M`.

## Attempts

- **Known bases.** Countable unions of closed finite-dimensional compacta: the bundle
  is trivial (`r-fibre-w-star-bundle-sigma-finite-dim-base-is-trivial`), hence the claim
  holds.
- **Local existence.** At `λ_0 ∈ K`, lift matrix units of `M_N ⊂ π_{λ_0}(M) = R` to `M`.
  The relation defects are continuous functions of `λ`, so the lift is a good system on a
  neighbourhood. No centrality is needed, so the neighbourhood depends only on the lift,
  not on earlier choices.
- **Orthogonal coloured gluing (heuristic).** Suppose a cover has `d + 1` colours of
  pairwise disjoint open sets, and local systems of different colours have orthogonal
  ranges wherever their pieces overlap.
  - A central partition of unity `ψ_i` gives `Φ = Σ_i ψ_i φ_i`. It is order zero, and it
    captures trace about `1/(d+1)`.
  - Iterating inside the remainder `1 − Φ(1)` would capture geometrically.
  - Two things are unproved. Arranging orthogonal ranges across colours, lifted at
    different points, is itself a gluing problem. And iteration needs local systems inside
    the remainder's hereditary subalgebra.
  - Even granting both, the capture per round is `1/(d+1)`, which tends to 0 with
    unboundedly many colours. So this scheme cannot reach strongly infinite-dimensional
    bases such as the Hilbert cube.
  - Heuristic analogy, not proved: selection theorems for non-convex values (Uspenskij,
    C-spaces) fail beyond C-spaces, and the Hilbert cube is not a C-space.
- **Infinite tensor products (Hirshberg–Rørdam–Winter type).** Let `B = ⊗_j B_j` over
  `X = ∏_j X_j`, with `B_j = End(θ ⊕ L_j)` for line bundles `L_j` over `X_j`. Its fibres are the
  CAR algebra and its trace simplex is `Prob(X)`, so the strict closure is an R-fibre bundle.
  This is the base algebra of Dadarlat–Hirshberg–Toms–Winter's non-embedding example.
  - **Tails give triviality.** Suppose every tail `⊗_{j>k} B_j` divides its unit tracially. A tail
    order zero `M_N` with trace near `1` commutes exactly with `⊗_{j≤k} B_j ⊗ 1`, and so is
    approximately central and approximately multiplicative. Ozawa's Theorem 15 (iii) then makes
    the bundle trivial. So an existence-gap witness of this type needs a tail with an indivisible
    unit.
  - **Characteristic classes see little (heuristic).** At stage `k` the unit is
    `E_k = ⊗_{j≤k}(θ ⊕ L_j)` of rank `2^k`. A tracial halving with rank defect `ρ` would give,
    if its pieces were bundles, `E_k ≅ W ⊕ W ⊕ R` with `rank R ≤ ρ`. In `K^0`,
    `[E_k] = Π_j(2 + t_j) ≡ Π_j t_j` mod 2, with `t_j = [L_j] − 1`. The mod-2 Chern-class
    obstruction lives in the square-free components, of complex degree at most `k`. It vanishes
    once `ρ ≥ k`, while `n = 2^k`. Unstable-range obstructions and the passage from order zero
    maps to bundles were not examined. So these products look unpromising as existence-gap
    witnesses.
- **Rotation gluing.** On an overlap, two local halvings with orthogonal equivalent pieces
  rotate into each other by central cosines. That needs partial isometries between local
  halvings.
  - Abstract bundles may lack them (Toms-type comparison certificates).
  - Strict closures of strict-comparison algebras have global approximate equivalence of
    equal-trace projections (`strict-comparison-bundle-certificate-vanishes`). Local
    versions on overlaps were not derived.
- **Face bundles of block-balanced towers divide (2026-09-12, lane
  `ex-tw-projection-starved-bundle`).**
  - **Where it holds.** The claim holds for every bundle over a closed set of extreme
    traces of an algebra with central halving
    (`central-halving-trivializes-every-closed-bauer-face-bundle`).
  - **Which towers have central halving.** Toms's towers, DHTW, HRW products and diagonal
    AH algebras, together with their corners (`block-balanced-towers-have-central-halving`).
  - **Tails.** For the infinite tensor products above, the projections `1 ⊗ e_j` are already
    norm-central with trace `1/2`. So the tail hypothesis of the first sub-bullet is not
    needed.
  - **Calibration.** In the Hopf doubling tower no finite stage has a nonzero square
    subbundle, yet the unit divides over every face
    (`hopf-doubling-tower-has-no-m2-but-divides-unit-tracially`). So finite-stage
    characteristic-class obstructions, including the mod-2 count in the tensor-product
    bullet, cannot refute this claim.
