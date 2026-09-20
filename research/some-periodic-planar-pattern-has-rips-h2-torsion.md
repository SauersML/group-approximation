---
rg: 2
id: some-periodic-planar-pattern-has-rips-h2-torsion
kind: claim
title: "Some translation-periodic planar pattern has a connected Rips complex whose second homology has nonzero torsion as a module over the translation"
distinct_from:
  some-finite-planar-set-has-a-non-wedge-rips-complex: that claim asks for a finite non-wedge; by route finite-planar-non-wedge-from-periodic-rips-h2-torsion this periodic statement implies it, and the converse is not known
  some-infinite-planar-set-has-a-non-wedge-rips-complex: a periodic pattern with H_2 torsion over the translation need not be a non-wedge itself (Z[t]/(t-1) is a free abelian group); the certificate only works after bending to finite sets
  some-planar-rips-chain-gadget-multiplies-a-sphere-class: the gadget asks for a multiplier of absolute value at least two, with separation (G2); here a unit multiplier suffices (t z = z or t z = -z is torsion), no separation is needed, and the pattern is periodic in both directions
artifacts:
  - experiments/planar-rips-periodic-strip-2026-09-17/periodic_rips.py
  - experiments/planar-rips-periodic-strip-2026-09-17/random_search.py
  - experiments/planar-rips-periodic-strip-2026-09-17/results.txt
---

There are a finite set `M ⊆ R^2`, a vector `v ≠ 0` and a scale `r > 0` with
the following properties. Let `Y = M + Zv`, with pairwise distinct points and
`r` generic in the sense of `periodic-planar-rips-patterns-bend-to-finite-quotients`.
Let `t` be the action of `τ(y) = y + v`. Then `R_r(Y)` is connected, and for
some field `k` the `k[t^{±1}]`-module `H_2(R_r(Y); k)` has a nonzero torsion
element.

**Finite certificate.** `C = C_*(R_r(Y); k)` is a free `k[t^{±1}]`-complex
with one basis element per `τ`-orbit of cliques. Its boundary coefficients
are `±t^s`, where `s` is the period shift of a face. For `λ ∈ k̄^×` let
`b_q(λ) = dim H_q(C ⊗ k̄_λ)`, and let `Δb_q(λ) = b_q(λ) − b_q(generic)`.
Put `T_q` for the torsion submodule of `H_q(C)` and
`d_q(λ) = dim(T_q ⊗ k̄_λ)`. The universal coefficient theorem over the PID
`k̄[t^{±1}]` gives `Δb_q = d_q + d_{q−1}`. Hence

  `d_2(λ) = Δb_2(λ) − Δb_1(λ) + Δb_0(λ)`,

and the claim holds iff `d_2(λ) > 0` for some `λ`. A jump of `b_2` alone may
come from torsion in `H_1`, such as a circle carried along the strip
(`S^1 × R`). That is why the alternating correction is needed. Unit sliding
of a sphere, `t z = ±z`, shows up at `λ = ±1`.

**Why it matters.** Route `finite-planar-non-wedge-from-periodic-rips-h2-torsion`
proves that this claim implies
`some-finite-planar-set-has-a-non-wedge-rips-complex`. That turns Attempt (B)
of the finite claim into one computable module question on a single period.
It also removes (B)'s separation requirement: clusters need not be more than
`r` apart, and the multiplicity relation `a = ±b` is enough.

## Attempts

- **2026-09-17, periodic strip search (swarm-0917-w20).** Scripts in
  `experiments/planar-rips-periodic-strip-2026-09-17/`:
  - `periodic_rips.py` computes the twisted Betti numbers mod `p = 2147483629`
    after equivariant dominated-orbit reduction. It is validated on
    `S^2 × R`: `[1,1,1]` at `λ = 1` and `[0,0,0]` otherwise.
  - `random_search.py` compares `b_2` at `λ = 1`, `λ = −1` and a random
    `λ`. Since `d_2 ≤ Δb_2`, the absence of any `b_2` jump certifies
    `d_2(±1) = 0`.

  Families and results:
  - `hexa`: 1–3 jittered octahedral hexagons per period, plus random points.
    2928 patterns; `H_2 ≠ 0` in 108, always free.
  - `box`: uniform motifs of 5–16 points. 2920 patterns; `H_2 ≠ 0` once, free.
  - `rows`: 2–5 horizontal rows. 2941 patterns; `H_2 = 0`.
  - `lattice`: square and triangular strips of 2–5 rows near critical
    lattice distances. 1680 patterns; `H_2 = 0`.
  - `octa`: one octahedral 6-set translated by a short vector `|v| ≤ 0.6`,
    the rigid sliding track. All 38 processed samples (22 more exceeded the
    cell cap) had `b_2 = 0` at `λ = 1` and generically. This family is small
    because dense tracks are expensive.

  No torsion was found. The sliding-track samples inspected by hand reduce to
  `b = [1, 1, 0]` at `λ = 1` (an `S^1`-like quotient) and `[0, 0, 0]`
  generically. So `H_2(R_r(Y))` has rank 0 and no class with `tz = ±z`: the
  carried sphere dies in `R_r(Y)` itself, not only in the quotient.
- **Where it stalls: cone points.** An octahedral sphere on a hexagon of
  circumradius `R` bounds as soon as some point of `Y` lies within `r` of all
  six vertices. That region contains a disc of radius `r − R ≥ 0.42 r`
  around the centre (for regular hexagons, `R ∈ (r/2, r/√3]`). A track that
  carries the sphere one full period moves its centre past its own earlier
  vertices, which then tend to enter later kernels. This is the suspected
  mechanism behind the collapses; it was not checked sample by sample. A proof
  that every octahedral slide track `O_0 → … → O_0 + v` in a periodic `Y`
  has a vertex coning one of its octahedra would kill octahedral classes
  for this claim. Sliding classes are `±` each other (chain-gadget §4.4),
  so one cone point kills the whole track. That proof is not written;
  non-octahedral `H_2` classes would remain.
- **Dense rigid tracks cannot be products.** Let `O` be octahedral with far
  pairs `(a_k, a_k')`. Suppose `|a_k − a_k' + sv| > r` for all real `s`.
  Then each far vector has perpendicular component `> r` with respect to
  `v`, while cross pairs have perpendicular gap `≤ r`. Let `u_k` be the
  higher and `l_k` the lower projection of pair `k`. Then
  `u_k ≤ l_l + r < u_l` for all `k ≠ l`, which is impossible. So in the
  continuous limit some antipodal pair becomes adjacent at some shift, and
  `O × R` never occurs as a strong product. For integer `s` the argument
  gives only inequalities with slack `r − (r^2 − |v|^2/4)^{1/2}`. For short
  `v` it is a heuristic, not a proof.
