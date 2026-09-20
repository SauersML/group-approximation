---
rg: 2
id: some-infinite-planar-set-has-a-non-wedge-rips-complex
kind: claim
title: "Some infinite planar set has a connected Rips complex that is not homotopy equivalent to a wedge of spheres"
distinct_from:
  rips-complexes-of-planar-sets-are-wedges-of-spheres: that claim is the universal positive statement over all subsets; this claim asks for one infinite counterexample
---

There are an infinite set `X ⊆ R^2` (Euclidean metric) and a scale `r > 0`
such that `R_r(X)` (with the closed or the strict diameter convention) is
connected and not homotopy equivalent to any wedge of spheres.

`some-finite-planar-set-has-a-non-wedge-rips-complex` implies this claim (add
infinitely many near-twins of one point; see that claim). This claim matters
separately only if the finite reading has a positive answer.

## Attempts

- Infinite sets allow critical scales where the closed and strict conventions
  differ, and complexes of infinite dimension. For the circle at its critical
  scales, Adamaszek–Adams report wedges of uncountably many even spheres
  (context, unverified here), which is still a wedge.
- No infinite-specific mechanism is recorded yet; the periodic-strip attack
  (C) on the finite negation produces finite sets.
- 2026-09-18 (swarm-0917-w10-w10-z-break): fundamental-group certificates are
  dead for countable sets. By
  `planar-rips-pi1-is-aleph1-free-and-free-when-countable`, `π_1(R_r(X))` is
  free for every countable `X ⊆ R^2`, and `ℵ_1`-free for every `X`.
  - The proof goes through the new planar lemma
    `planar-polyhedron-inclusions-have-free-factor-pi1-images`. That lemma
    closes the gap recorded in §6 of
    `research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md`.
  - Together with free `H_1` (`planar-rips-complexes-have-free-first-homology`),
    a countable counterexample must be certified in degree `≥ 2`: by `π_{≥2}`,
    `H_{≥2}`, the `π_1`-action on higher homotopy, or `k`-invariants.
  - A non-free `π_1` remains a possible certificate only for uncountable `X`.
    There it would have to be a non-free `ℵ_1`-free group. The precise missing
    coherence statement is recorded in the Attempts of the `π_1` claim.
  - This claim stays open.
- 2026-09-20 (swarm-0917-w23-w23-z-pull): full-spectrum census of the
  periodic mechanism; negative. For a periodic pattern `Y = M + Zv`,
  `H_2(R_1(Y))` is a module over `L = k[t^{±1}]`. Torsion at an eigenvalue
  `λ = m ≠ ±1` (over `Z`) gives an infinitely divisible class in `H_2`, so
  `R_1(Y)` is not a wedge; torsion at any `λ` also bends to a finite
  non-wedge. The 2026-09-17 periodic-strip search tested only `λ = ±1`.
  - Method: exact Smith form over `F_p[t^{±1}]` (`p = 2147483629`) of the
    equivariant `∂_3`, after dominated-orbit reduction. Torsion of `H_2`
    equals torsion of `coker ∂_3`, because `B_1` is free over the PID. The
    invariant factors are factored over `F_p`, so every eigenvalue in the
    algebraic closure of `F_p` is covered.
  - Validation: hand-made Laurent matrices, including a scrambled
    `diag((t-5)(t-7), t-5, 1)`, all come out right. The octahedron `× Z`
    gives `{t-1}`, and its orientation-reversing twist gives `{t+1}`.
  - Census: 22,490 patterns over 8 families.
    - Old families: hexa, box, rows, lattice, octa.
    - New `circ` family: cyclic `3m`-gons at their wedge-of-`S^2` scales.
    - New `hexpair` family: two octahedral hexagons per period.
    - New `dbox` family: dense boxes.
    - Result: zero torsion at every eigenvalue.
  - Stronger: in every pattern, monomial (unit) pivots alone reduce `∂_3`
    to the empty matrix. So `H_2` is a free `L`-module, not merely
    torsion-free at `±1`. 867 patterns have `H_2` of positive `L`-rank,
    which is still a wedge-compatible outcome.
  - Caveats: the computation is over `F_p`. Over `Q[t^{±1}]` it misses
    only factors that are congruent to a monomial mod `p`. Small-prime
    `Z`-torsion is not tested.
  - Artifacts: `experiments/planar-rips-full-spectrum-2026-09-17/results.txt`
    and `laurent_smith.py`, `full_spectrum.py`, `search.py` in the same
    directory.
  - Suggested next prerequisite (it can fail on its own): "after
    dominated-orbit reduction, the equivariant `∂_3` of every periodic
    planar Rips complex is unit-pivot reducible". If true, it kills the
    periodic-torsion route to both the finite and the infinite claims. A
    counterexample would have to come from structure outside these
    families.
