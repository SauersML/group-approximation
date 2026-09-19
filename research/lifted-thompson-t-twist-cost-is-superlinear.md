---
rg: 2
id: lifted-thompson-t-twist-cost-is-superlinear
kind: claim
title: "The twist cost of T-bar is superlinear at 0: c(θ)/‖θ‖ → ∞ as θ → 0, because a linear-rate twist family rescales to a cocycle whose invariant projection is a nonzero homomorphism of the perfect group T-bar; the halving endomorphism g ↦ D^{-1}gD gives min(c(θ/2), c((θ+1)/2)) ≤ √2·M·c(θ)"
distinct_from:
  lifted-thompson-t-relative-t-forces-dyadic-twist-gap: that defines c and proves the linear lower bound c(θ) ≥ |e(θ)−1|/L; this proves c is not even comparable to ‖θ‖ from above near 0, and adds the halving inequality
  perfect-extension-splittings-are-not-uniformly-integrable: that kills uniformly integrable measurable Euler splittings with Koopman almost invariant vectors; this is a statement about arbitrary unitary representations with scalar z, with no space and no splitting
  lifted-thompson-t-extractable-cocycles-bounded-on-centre: that bounds the centre for representations with a circle extraction; this constrains all representations, but only at first order in the twist
---

**ESTABLISHED** by `lifted-thompson-t-twist-cost-is-superlinear-proof`.

**Notation.** `T̄`, `z`, `S`, `L`, `e(θ)` and the twist cost `c` are as in
`lifted-thompson-t-relative-t-forces-dyadic-twist-gap`. `‖θ‖` is the distance from `θ` to `Z`.
`D(x) = 2x`, and `t_{1/2}(x) = x + 1/2`, which lies in `T̄` (it lifts the rotation by `1/2`).

**Theorem.**
1. *(Superlinearity.)* `c(θ)/‖θ‖ → ∞` as `θ → 0` in `R/Z`, `θ ≠ 0`. Equivalently: there is no
   sequence `θ_n → 0`, `θ_n ≠ 0`, with unitary representations `π_n` of `T̄`, `π_n(z) = e(θ_n)·I`,
   and unit vectors `ξ_n` with `max_{s∈S} ‖π_n(s)ξ_n − ξ_n‖ ≤ K|θ_n|` for a fixed `K`.
2. *(Linear regime is where subadditivity works.)* If `σ = liminf_{θ→0} c(θ)/‖θ‖` were finite,
   then `c(x) ≤ σ‖x‖` for every `x ∈ R/Z`. By item 1 this never happens, so the lower
   semicontinuity plus subadditivity ("net of multiples") argument cannot transfer small
   non-dyadic twist costs to dyadic ones.
3. *(Halving.)* `Φ(g) = D^{-1} g D` is an injective endomorphism of `T̄` with `Φ(z) = t_{1/2}`
   and image in the centralizer of `t_{1/2}`. With `M = max_{s∈S} |Φ(s)|_S`, for every `θ`
   (read with a real representative), `min(c(θ/2), c((θ+1)/2)) ≤ √2 · M · c(θ)`.

**Class killed (item 1).** Every "first-order" construction of small twists dies: any family in
which the almost-invariance defect of a unit vector is `O(|θ|)` as the scalar `e(θ)` of `z` tends
to `1`. This includes
- characters or deformations `θ ↦ π_θ` that are differentiable at `θ = 0` in the sense that
  `(π_θ(s)ξ_θ − ξ_θ)/θ` stays bounded;
- twisted Koopman families `e(θβ)·κ` with `‖κ(s)ξ_θ − ξ_θ‖ = O(|θ|)` and
  `‖β(s,·)·κ(s)ξ_θ‖_2` bounded (this case is also inside (F1) of
  `thompson-t-euler-class-splits-over-almost-invariant-space`).

The invariant is `H^1(T̄, 1) = Hom(T̄, C) = 0`. The step where every member dies: the ultralimit
of the rescaled cocycles `(π_n(g)ξ_n − ξ_n)/θ_n` has a nonzero component on invariant vectors at
`z`, and that component is a homomorphism of `T̄`.

**What this does to the open items.**
- For `lifted-thompson-t-is-a-t-menable`: a witness must realise `inf_{θ≠0} c = 0` through
  costs with `‖θ‖ = o(c(θ))`. Twist families produced by differentiating at the trivial
  representation are excluded.
- For the reduction "non-dyadic ⇒ dyadic" left open in the dyadic-twist-gap node: item 2 shows
  the only regime in which lower semicontinuity and subadditivity alone transfer smallness is
  empty. Item 3 moves twists inside `θ/2 + {0, 1/2}` at multiplicative cost `√2M`, and so keeps
  an irrational `θ` in `Z[1/2]θ + Z[1/2]`. Heuristically (not established), no chain of these
  exact moves reaches a small nonzero dyadic point from an irrational one, except through
  constant branch values that are not small. The reduction stays **open**.

**Novelty.** The rescaling-to-a-homomorphism step is the standard argument that groups with
`H^1 = 0` have no first-order deformations of the trivial representation. Not independently
reviewed.
