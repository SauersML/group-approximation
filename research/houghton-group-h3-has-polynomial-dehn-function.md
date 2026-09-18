---
rg: 2
id: houghton-group-h3-has-polynomial-dehn-function
kind: claim
title: "Houghton's group H_3 has a polynomially bounded Dehn function"
distinct_from:
  houghton-group-h4-has-polynomial-dehn-function: that is the four-ray case, where route changes of pours exist; with three rays a pour E^c_(a,b) has a unique route c, so the pour method has nothing to change.
  houghton-groups-have-polynomial-dehn-function: that is the statement for every n >= 3; this is the single case n = 3.
---

There is an integer `d` with `δ_(H_3)(x) ≼ x^d`.

## Attempts

- 2026-09-18 (swarm-0917-w8-w8-z-break). Recorded as the three-ray case of the
  split of `houghton-groups-have-polynomial-dehn-function` by ray count. All pour
  arguments (`research/artifacts/zp-houghton-pours-2026-09-17.md`,
  `research/artifacts/zp-houghton-five-rays-2026-09-17.md`) need at least four rays:
  - with three rays, `E^c_(a,b)` has only one possible route;
  - the edge-commutation steps (Theorem 3.1, Proposition 4.1(ii)) choose four
    distinct rays.

  The loops `λ_12^m λ_23^m λ_31^m` are finitary permutations, not trivial words.
  Lee's exponential bound is the only upper bound known for this case.
- 2026-09-18 (swarm-0917-w10-w10-z-follow). Reframing, in
  `research/artifacts/zp-houghton-three-rays-2026-09-18.md`.
  - **Established.** `houghton-h3-dehn-polynomial-iff-five-three-ray-families`
    reruns the six-ray path-word proof with `n = 3`. Every step there that needed a
    spare ray becomes one of five explicit linear-length families
    (`F_3, R_3, B_3, C_3, D_3`). This gives `δ(L) <= C L^6 (Φ(L+C) + L)` and
    `Φ(L) <= δ(CL)`. The new route `houghton-h3-polynomial-dehn-via-five-families`
    needs only the open family bound
    `houghton-h3-five-three-ray-families-have-polynomial-area`.
  - **Proved partial step.** A doubling endomorphism `Δ` with `Δ(λ_ba) = λ_ba^2`
    reduces the even-scale `F_3` and `R_3`, at constant factor, to depth-`k`
    hidden-top relators. The recursion does not close: those relators are bounded
    only at scale `16k`, and `Δ` reaches only even permutations and even scales.
  - **Killed.** By the ray-support invariant, every "reroute to disjoint ray
    supports, then commute letterwise" argument dies at the commute step for
    `n = 3` (Lemma C.1).
- 2026-09-18 (swarm-0917-w12-w12-z-follow, calibration/referee). This was a referee pass
  on the two unrefereed inputs of the wave-12 closure (lane z-last1; not merged into this
  worktree). Those inputs are Theorem A of wave 10, `δ_(H_3)(L) <= C L^6 (Φ(L+C) + L)`,
  and the doubling Prop 5 `A(2m) <= K A(m)`.
  - **Machine check of the three-ray edge layer.** This is the new claim
    `houghton-h3-edge-relations-reduce-to-five-families`, with complete proof
    `houghton-h3-edge-relations-via-free-product-normal-form`. Each three-ray edge relation
    (E1)–(E3), and each Lemma 4.2 letter relation, costs at most two literal five-family
    relators plus `30R`. These are Theorem A's A.2 and A.3 in sharper form. The checker
    `experiments/houghton-h3-theorem-a-2026-09-17/verify_theorem_a.py` replays all 31680
    relations for all 8 route functions at depth `<= 20`. It measures `<= 8R + 2` `Q`-steps
    and finds no hidden use of a fourth ray. (E2)(v) has no instance for `n = 3`.
  - **Hand audit of the remaining steps.** The §5 path-word lemmas and Theorem 6.1
    (steps 1–4) do not depend on `n`, and they pass. Lemma 5.2 for `n = 3` uses all three
    tops. Corollary 5.3 has `q <= 2`. In Lemma 5.6, `m = (w,1)` is forced and off the
    image path. The sorting and elimination of the 09-13 note are valid for `n >= 3`.
  - **Hand audit of Prop 5.** The letterwise lift and its odd step are sound. The
    constant `K` is not explicit, and the area recursion is not machine-checked.
  - The §5/§6 layer and the z-last1 macro areas are still checked only by hand. This
    claim stays OPEN in this worktree until the z-last1 route lands.
