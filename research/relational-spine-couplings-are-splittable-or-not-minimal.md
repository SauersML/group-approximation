---
rg: 2
id: relational-spine-couplings-are-splittable-or-not-minimal
kind: claim
title: Over the end flow, a relational space coupling of seeded phases either splits or kills minimality, while the functional coupling with a transitive time clock is minimal as well as quantum rigid
requires:
  - seeded-transport-codings-over-end-flows-are-quantum-rigid
  - end-shift-path-covers-are-rigid-with-one-spine
  - minimal-sfts-with-a-finite-modification-are-not-quantum-rigid
distinct_from:
  seeded-transport-codings-over-end-flows-are-quantum-rigid: that proves rigidity for bijective space transport; this replaces the bijection by a relation, and settles minimality for both.
  nonamenable-products-have-minimal-sft-extensions-of-free-inputs: its phase-field trichotomy is a heuristic about hierarchy phases on unanchored grids; this is a proved dichotomy for seeded finite phases over the end flow, where the functional case turns out to be minimal.
---

**ESTABLISHED (lane bh-g2-fixedpoint-b, 2026-09-18; elementary lane proofs, not reviewed; no
priority claimed).** This tests one relational coupling, as asked, and reverses an expectation
recorded on `seeded-transport-codings-over-end-flows-are-quantum-rigid`.

## Setting

- **Groups and base.** `Λ = H × F_m`, with `H = <S_H>` infinite and `m >= 2`. The base is
  `pt ⊠ X_∂(F_m)`, the end flow, constant along `H`. `τ`, the spine `ℓ_η`, and `Σ_ν` are as in
  `end-shift-path-covers-are-rigid-with-one-spine`.
- **Computation.** A finite set `C` with the following rules. The time rule and the seeds read only
  the flow; they are *H-blind*.
  - **(Ti)** `c(λ, v') = β(c(λ, parent v'))` if `v'` is a rank-2 child, with `β ∈ Sym(C)`.
  - **(Se)** `c(λ, v') = κ` otherwise.
  - **(R)** For each `s ∈ S_H^+`, a chosen generating set of `H`: `(c(λ, v'), c(λs, v')) ∈ R_s`,
    with `R_s ⊆ C × C`.
- **The spine phase shift.** Over `η ∈ Σ_ν`, index `ℓ_η` downward by `t ∈ Z`, so `ℓ(t+1)` is the
  rank-2 child of `ℓ(t)`. A completion on the sheet is `c(λ, ℓ(t)) = β^t(ψ(λ))`, with
  `ψ ∈ Φ_R := {ψ ∈ C^H : (β^t ψ(λ), β^t ψ(λs)) ∈ R_s for all t, λ, s}`. `Φ_R` is an `H`-SFT.
- **Effective relation.** `R̂_s = {(x, y) : (β^t x, β^t y) ∈ R_s for all t}`. The coupling is
  *functional* when every `R̂_s` is the diagonal; then `Φ_R` consists of constants, since `S_H^+`
  generates `H`. Otherwise it is *relational*.

## Theorem

1. **Anchored values ignore space.** Over an end `η ∉ Σ_ν`, the completion is unique and
   `c(λ, v') = β^(τ(v'))(κ)` for all `λ`. Hence `Z_R ≠ ∅` forces every `R_s` to contain the diagonal
   of the `β`-orbit of `κ`.
2. **Minimality dichotomy.** `Z_R` is minimal if and only if every `ψ ∈ Φ_R` is constant with value
   in the `β`-cycle of `κ`. When `R_s` contains the full diagonal, this means `Φ_R` is constant and
   `β` is one cycle on `C`.

   In particular, every coupling that admits a non-constant spine phase field kills minimality.
3. **The functional clock is minimal and rigid.** For `C = Z/q`, `β(c) = c + 1`, `κ = 0` and
   `R_s = diagonal`, `Z` is minimal and quantum rigid over every field. It is also topologically free
   for the `F_m`-action, on which `H` acts trivially.
4. **Relational couplings split, or are not minimal.** Three tests. None of them is minimal, by item 2,
   since each admits non-constant spine phase fields.
   - **(a) Clock with increments.** Take `β(c) = c + 1` on `Z/q`. Then `Φ_R` is cut out by increment
     sets `I_s = {d : (x, x+d) ∈ R_s for all x}`, which contain `0`. Take `H = Z × H'`,
     `S_H^+ = {s} ∪ S_(H')`, and `I_t = {0}` for `t ∈ S_(H')`. If `I_s` contains some `g ≠ 0`,
     then `Z_R` is not `D`-rigid for any `D`, and it is splittable.
   - **(b) One-way step, no clock.** Take `β = id`, `C = {0,1}`, `H = Z = <s>`, and
     `R_s = {(0,0), (1,1), (0,1)}`. Then `Φ_R = {0^Z, 1^Z} ∪ {1_[a,∞) : a ∈ Z}`, a copy of the
     two-point compactification of `Z`, as in `C_Z`. Over a fixed base point, no configuration has
     two modifications whose supports are more than `1` apart, so it is unsplittable. But `Z_R` is
     not minimal, by item 2.
   - **(c) One-way coupling on a tree.** The same relation on `H = F_2 = <a, b>`, with
     `S_H^+ = {a, b}`. The spine phase fields include `1_(λM)` for the positive monoid `M`. The
     modifications `1_(a^N M)` and `1_(b^N M)` of `0` lie at distance `2N`, so `Z_R` is not
     `D`-rigid for any `D`.

## Proof

**1.**
- *Uniqueness.* Every chain from `v'` climbs to a seed at finite height. So `c(λ, v')` is
  `β^(τ(v'))(κ)`, with no dependence on `λ`.
- *The diagonal.* These values satisfy (R) only if `(x, x) ∈ R_s` for every `x` so realized.

**2, "only if".**
- *A closed invariant set.* `K = {z : c(λ s, v') = c(λ, v') for all λ, s, v'}` is closed and
  invariant, and by item 1 it contains every point over `X_∂ \ Σ_ν`. It therefore contains the orbit
  closure of any such point.
- *First condition.* A spine completion with non-constant `ψ` lies outside `K`, so `Z_R` is not
  minimal.
- *The value condition.* By item 1, every anchored point takes all its values in the `β`-cycle of `κ`,
  and so does every limit of anchored points. A spine completion with a value outside that cycle is
  not such a limit.

**2, "if", and 3.** Assume every `ψ ∈ Φ_R` is constant with value in the `β`-cycle of `κ`. Then `c`
does not depend on `λ`, `H` acts trivially, and it suffices to work over `F_m`.
- *(i) Anchored points are dense.*
  - Take a spine point `z'` with end `η'`, and fix `R_0`. Choose `u ∈ ℓ_(η')` far up, above every
    meeting point of the rays from `B_(R_0)`, with `c'(u) = κ`. Such `u` exist arbitrarily far up:
    going up, the spine values run through the `β`-cycle of the spine value, which is that of `κ`.
  - *Build `η''`.* Keep every arrow in the subtree of `u`, including the arrow of `u`. Give its
    parent `p_0 = u x'(u)` a new arrow `r ≠ x'(u)^(-1)` for which `u` is not the rank-2 child of
    `p_0`, and continue the ray from `p_0` generically, outside `Σ_ν`.
    - *Such `r` exists.* List `S` as `e_1 < e_2 < …`. The second element of `S \ {r}` is `e_3`
      for `r ∈ {e_1, e_2}`, and `e_2` otherwise. So take `r = e_1` if `x'(u)^(-1) = e_2`, take
      `r = e_4` if it is `e_3`, and any admissible `r` otherwise.
    - *What is unchanged.* `B_(R_0)` lies in the subtree of `u`, and so do its rays, with every
      rank below `u`.
  - Now `u` is a seed, and spine vertices below `u` get `β^(d(·,u))(κ) = c'`.
  - Vertices of `B_(R_0)` off the spine keep their chains, which never enter the spine: a chain enters
    a spine vertex only through its rank-2 child, which lies on the spine.
  - So the anchored point over `η''` agrees with `z'` on `B_(R_0)`.
- *(ii) Continuity.* On `X_∂ \ Σ_ν`, the completion `η ↦ c_η` is continuous. The chains from
  `B_(R_0)` stop within a bounded region, and nearby ends have the same chains.
- *(iii) Orbits.* `X_∂` is minimal. Let `z` be any point, and `z''` an anchored point.
  - Choose `g_k` with `g_k η(z) → η(z'')`.
  - The chains of `B_(R_0)` in `z''` stop inside some ball `B_N`. `g_k z` agrees with `z''` on the
    flow in `B_N` for large `k`, so the same chains stop there, before any spine.
  - Hence `g_k z → z''`.
- *(iv) Conclusion.* By (i), every orbit closure contains all points. So `Z` is minimal.
- *Rigidity* is `seeded-transport-codings-over-end-flows-are-quantum-rigid`, with `α = id`.
- *Topological freeness.* Suppose `g` fixed a nonempty open set of `Z`. It contains a cylinder `U`
  around an anchored point, prescribing the flow on `B_N` and the letters on `B_(R_0)`, where the
  chains of `B_(R_0)` stop inside `B_N`. Every end in the flow cylinder has a completion in `U`, so
  `π(U)` is a nonempty open set of fixed ends of `g`. The end shift has none.

**4(a).**
- *Increment sets.* A spine completion has `c(λ, ℓ(t)) = ψ(λ) + t`. So (R) at every `t` says
  `ψ(λ s) - ψ(λ) ∈ I_s`.
- *A bump.* Let `k` be the order of `g`. Put `ψ_a(j, h') = (j - a) g` for `a <= j <= a + k`, and `0`
  elsewhere. Every `s`-increment is `0` or `g`, every `H'`-increment is `0`, and the support is the
  slab `{a+1, …, a+k-1} × H'`.
- *Far modifications.* Take `η ∈ Σ_ν` and the completion `ψ ≡ 0`. Two bumps at `a` and `b`, with
  `|a - b| > 2D + k`, are modifications supported on slabs `× ℓ_η` at distance `> 2D`. The
  far-modification Lemma of `minimal-sfts-with-a-finite-modification-are-not-quantum-rigid` then
  refutes `D`-rigidity.

**4(b).**
- *The shift.* `Φ_R` is the set of non-decreasing `{0,1}`-sequences, as listed.
- *Supports meet.* Check the modifications of each point.
  - Of `0^Z`: every support contains a half-line to `+∞`.
  - Of `1^Z`: every support contains a half-line to `-∞`.
  - Of the step `1_[a,∞)`: every support contains `a - 1` or `a`.
  So any two supports are within distance `1`, and this persists on the sheet.
- *Not minimal.* The steps are non-constant.

**4(c).**
- *The fields.* `ψ` must be non-decreasing along `·a` and `·b`, so indicators of sets closed under
  `·a` and `·b` qualify, such as `λM`.
- *The distance.* For positive words `w, w'`, the word `w^(-1) a^(-N) b^N w'` is reduced: nothing
  cancels at any junction. So `d(a^N M, b^N M) >= 2N`.
- *Far modifications.* As in 4(a). ∎

## Comparison with bh-g2-fixedpoint-a (crossing-wire fixed-point tiles)

That lane has rigid, aperiodic `Z^2` tile sets and needs minimality. The mechanism here is
**boundary completeness**: minimality follows from base minimality once every unseeded completion is
a limit of seeded configurations, as in step (i).
- The analogue for a fixed-point tile set: every infinite-level completion of the macrotile
  hierarchy is a limit of finite-level (seeded) ones.
- Its failure mode is item 2's second condition. A completion class that seeds never reach, such as
  a second `β`-cycle, is an unreachable invariant set.

## Lesson for general BH

Among H-blind seeded phase codings over the end flow, minimality forces every configuration to be
constant in space, with values in one time cycle. The coding then coincides, as a subshift, with a
functional clock: rigid by the downhill theorem, and minimal by boundary completeness.
- **Relational freedom is fatal.** It either splits: finite phases wrap around (4a), and trees
  separate cones (4c). Or it creates spine configurations that seeds never approach (4b), which kills
  minimality.
- **So relational coupling is not the E1 ∧ E2 crux here.** The expectation recorded on
  `seeded-transport-codings-over-end-flows-are-quantum-rigid` is reversed: functional couplings give
  minimality for free.
- **What these codings lack is input complexity.** H-blind seeds compute only time mod `q`. The live
  question is v6's CAP: can seeded transport carry a word problem? That requires seeds or transports
  that read the input's data, and whether the downhill theorem survives such reading.
