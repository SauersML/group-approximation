---
rg: 2
id: every-free-of-infinity-artin-group-is-type-f-infinity
kind: claim
title: Every Artin group whose Coxeter graph has only finite labels is of type F_infinity
---

For every finite set `S` and Coxeter matrix on `S` with `m_st < ∞` for all `s ≠ t`, the
Artin group `A_Γ` is of type `F_∞`.

By `artin-type-f-n-reduces-to-free-of-infinity-graphs` this is equivalent to
`every-artin-group-is-type-f-infinity`, and the route
`artin-f-infinity-from-free-of-infinity-case` records the direction that matters: only
graphs with all labels finite need attention.

**Where the open cases are.** For a free-of-infinity graph, FC type is the same as
spherical type. The K(π,1) results listed in the root
`zaremsky-1-05-artin-groups-are-type-f-infinity` give type F, hence type `F_∞`, for
free-of-infinity graphs of spherical, affine or rank-three type, of dimension `≤ 2`, in
Huang's classes (arXiv:2305.16847, arXiv:2405.12068), and, by the preprint
arXiv:2509.06914 of Huang and Przytycki, of dimension 3. Here the dimension is the largest
size of a subset generating a finite Coxeter group. So a free-of-infinity graph not yet
covered has dimension at least 4 and an infinite Coxeter group, hence rank at least 5
(in rank 4, dimension 4 forces the whole graph to be spherical), and lies outside the
listed classes. Lane z1-05-artin-kpi1 is assembling the exact list.

## Attempts

Direct side, lane z1-05-artin-direct, 2026-09-13; details and sources in
`research/artifacts/zp-artin-direct-f-infinity-2026-09-13.md`.

- **Brown's criterion on the modified Deligne complex `Φ(A)`** (cocompact, cell
  stabilizers spherical parabolic subgroups, which are of type F by Deligne). It gives
  type `F_n` when `Φ(A)` is `(n − 1)`-connected. Since `Φ(A)` is homotopy equivalent to
  the universal cover of the Salvetti complex (Charney–Davis 1995), type `F_∞` this way
  needs `Φ(A)` contractible, which is the K(π,1) conjecture for `A`. Dies: the route
  coincides with the K(π,1) route.
- **Brown's criterion on the Artin complex `Δ(A)`** (cosets of the maximal standard
  parabolic subgroups; cocompact, stabilizers proper parabolic subgroups; induction on
  rank). When the proper parabolic subgroups satisfy the K(π,1) conjecture, the nerve
  theorem gives `Δ(A) ≃ Φ(A)`, so this route needs the same connectivity. Unconditionally
  `Δ(A)` is connected for `|S| ≥ 2` and simply connected for `|S| ≥ 3`, because `A` is the
  colimit of its maximal standard parabolic subgroups along their pairwise intersections
  (every defining relation involves only two generators). That recovers finite
  presentability and nothing more. Its top homology is the left ideal
  `⋂_s ZA·(1 − s)` (`artin-complex-top-homology-is-intersection-of-ideals`).
- **Homotopy-module criterion** (`artin-type-f-k-plus-1-iff-salvetti-pi-k-fg`): type `F_3`
  holds iff `π_2(Sal(A))` is a finitely generated `ZA`-module, and so on up the degrees.
  The first open step is finite generation of `π_2(Sal(A))` for an uncovered
  free-of-infinity graph. The stronger conjecturette `π_2(Sal(A)) = 0` is open in general
  (R. Boyd, arXiv:2601.08658, §2.3.7). No mechanism is known that gives finite generation
  without vanishing.
- **Two-out-of-three for `FP_∞` modules.** The chain modules of `Φ(A)` are permutation
  modules `Z[A/A_U]` with `A_U` of type F, hence of type `FP_∞`. Since `FP_∞` modules have
  the two-out-of-three property in short exact sequences, `A` is of type `FP_∞` whenever
  every `H_i(Φ(A))` with `i ≥ 2` is an `FP_∞` module over `ZA`. No handle on these modules
  is known other than their vanishing.
- **Subgroups, quotients, retractions.** The kernel of `A → W` is the fundamental group of
  the hyperplane complement, which is no easier. The Salvetti complex of a standard
  parabolic subgroup is a `W_T`-equivariant retract of the whole Salvetti complex
  (Godelle–Paris; arXiv:1211.7339, Theorem 5.1). That transfers asphericity downward
  (Theorem 5.5) but not finite generation of homotopy modules, since restriction to an
  infinite-index subgroup does not preserve finite generation. No retraction onto a group
  of known type is available in general.
