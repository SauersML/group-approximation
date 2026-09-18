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
