---
rg: 2
id: edge-split-descent-reaches-very-close-lattice-points
kind: claim
title: A lattice point very close to an irrational direction inside a unimodular cell becomes a ray of an edge-split descendant that still contains the direction
distinct_from:
  edge-splits-cut-every-rational-hyperplane: that cuts a cell along one hyperplane by a Euclid potential on its coefficients; this reduces the coordinate vector of one lattice point to a unit vector while keeping a nearby irrational direction inside every cell of the path.
  edge-split-cells-share-rays-at-totally-irrational-directions: that is the shared-ray statement at every totally irrational direction (OPEN); this proves it at the very well approximable ones.
  rank-two-synchronization-off-totally-irrational-rays: that decides descent of cells sharing a ray; this manufactures a shared ray from a good rational approximation.
---

**ESTABLISHED** (lane bh-major-mcg-2, 2026-09-18). Lane proof, elementary, not
independently reviewed. No priority claimed.

## Statement

Notation of `edge-splits-cut-every-rational-hyperplane`.

**Lemma (Legendre-type capture).**
- **Data.** A unimodular cell `g ⊂ R^{m+1}` with frame `U`, a ray `ξ ∈ int g` lying on
  no rational hyperplane, and a primitive lattice vector `p ∈ int g`.
- **Quantities.** `κ = U^{-1}p ∈ Z_{≥1}^{m+1}`, `K = |κ|_∞`, and
  `ε_g(p, ξ) = inf_{t > 0} |t U^{-1}ξ − κ|_∞`.
- **Conclusion.** If `ε_g(p, ξ) < 1 / (2 (m+1)! K^m)`, then some cell of `Desc(g)` has
  `p` as a ray and contains `ξ`.

**Corollary (very well approximable directions).**
- **Hypothesis.** `ξ` is totally irrational, `c, F` are cells with `ξ ∈ int c ∩ int F`,
  and
  `liminf_{p primitive, |p| → ∞} |p|^m · dist(p, Rξ) = 0`.
- **Conclusion.** Some `c_1 ∈ Desc(c)` and `f_1 ∈ Desc(F)`, both containing `ξ`, share
  a ray. So `(TI_m)` of `edge-split-cells-share-rays-at-totally-irrational-directions`
  holds at `ξ`.
- **Scope.** This covers every `ξ ∝ (1, α)` whose simultaneous approximation exponent
  exceeds `m`, that is, `|qα − p⃗|_∞ < q^{−ω}` for infinitely many `q` with some
  `ω > m`. That set has Lebesgue measure zero but contains a dense `G_δ` (the vectors
  with `ω = ∞`). It misses the generic and the badly approximable directions, whose
  exponent is `1/m`.

## Proof of the lemma

Scale so that `λ = t U^{-1}ξ` has `|λ − κ|_∞ < 1/(2(m+1)!K^m)`, and put
`δ = λ − κ`. Work in the coordinates of `g`, so `g = Δ` and `p = κ`.

- **The path.** While `κ` has at least two positive entries, pick `a ≠ b` with
  `κ_a ≥ κ_b ≥ 1`.
  - If `κ_a > κ_b`, split along `(a, b)` and keep the child that replaces `x_b` by
    `x_a + x_b`. In coordinates this is `κ_a ↦ κ_a − κ_b` and `λ_a ↦ λ_a − λ_b`.
  - If `κ_a = κ_b`, do the same with `(a, b)` or `(b, a)`, choosing the one with
    `λ_a > λ_b`. `λ_a ≠ λ_b`, because `ξ` misses the rational hyperplane
    `x_a = x_b` of the current cell.
- **Notation.** At stage `s` the frame is `X_s ∈ 𝕄`, with `κ^{(s)} = X_s^{-1}κ`,
  `λ^{(s)} = X_s^{-1}λ` and `δ^{(s)} = X_s^{-1}δ = λ^{(s)} − κ^{(s)}`.
- **Termination.** `|κ^{(s)}|_1` drops by `κ_b ≥ 1` at each step. `κ^{(s)}` stays a
  nonnegative primitive integer vector. So the path stops at a unit vector `e_i`, and
  there `p = X e_i` is a ray.
- **The columns stay below `p`.**
  - Initially the columns are the `e_k`, and `e_k ≤ κ` because `κ ≥ 1`.
  - At a step, `κ = Σ_k κ^{(s)}_k x_k ≥ x_a + x_b` entrywise, since
    `κ^{(s)}_a, κ^{(s)}_b ≥ 1`. So the new column `x_a + x_b` is again `≤ κ`.
  - Hence `X_s` has entries in `[0, K]`.
  - `X_s^{-1} = ± adj X_s`, and each `m × m` minor has absolute value at most `m! K^m`.
    So `|X_s^{-1}|_{∞→∞} ≤ (m+1)! K^m`, and `|δ^{(s)}|_∞ < 1/2` at every stage.
- **`ξ` stays inside.** Use induction on `s`, with `λ^{(s)} > 0`.
  - A step with `κ_a > κ_b` has
    `λ_a − λ_b = (κ_a − κ_b) + (δ_a − δ_b) > 1 − 1 = 0`.
  - A tie step has `λ_a − λ_b > 0` by choice.
  - So the one changed coordinate stays positive, and every cell of the path contains
    `ξ`.
- **Conclusion.** The last cell has `p` as a ray and contains `ξ`. ∎

## Proof of the corollary

- **Setup.** Let `W, U` be frames of `c, F`, and `N = max(‖W^{-1}‖, ‖U^{-1}‖)` in the
  `∞`-operator norm. Take primitive `p` along a sequence with
  `|p|^m · dist(p, Rξ) → 0`, replacing `p` by `−p` where needed so that `p` is close to
  the positive ray. Then `|p| → ∞`, because `ξ` is irrational.
- **Both cells contain `p`.** `dist(p, Rξ)/|p| → 0`, so `p` converges to `ξ` as a ray.
  For large `|p|`, `p ∈ int c ∩ int F`.
- **The threshold holds in both frames.** In the frame of `c`:
  - `K ≤ N|p|`;
  - `ε_c(p, ξ) ≤ N · dist(p, Rξ)`, choosing `t` with `tξ` the nearest point;
  - so `ε_c K^m ≤ N^{m+1} |p|^m dist(p, Rξ) → 0`.
  The same holds in the frame of `F`. So for large `|p|` the lemma applies in both.
- **The shared ray.** `p` is a ray of some `c_1 ∈ Desc(c)` and of some
  `f_1 ∈ Desc(F)`, both containing `ξ`.
- **Scope.** For `ξ ∝ (1, α)` and `p = (q, p⃗)`, `dist(p, Rξ) ≤ |qα − p⃗|` and
  `|p| ≍ q`. So `ω > m` suffices. ∎

## Remarks

- **Why the constant is crude.** The bound `|X_s^{-1}| ≤ (m+1)! K^m` is the worst
  case, where the cells of the path are thin.
  - On the other hand, the rows of the final `X^{-1}` other than row `i` form a basis
    of the rank-`m` lattice of integral forms vanishing on `p`. That lattice has
    covolume `|p|`, so by Minkowski some such row has norm at least a constant times
    `|p|^{1/m}`.
  - So `|X^{-1}|` is at least of order `K^{1/m}` on every path. Even on the best paths,
    the capture threshold can reach at most the Dirichlet scale `K^{-1/m}`.
  - Even then, constants decide whether Dirichlet's approximations are captured. So
    this mechanism is not known to settle `(TI_m)` at the generic or badly
    approximable directions.
- **Rank one.** For `m = 1` the lemma is a weak form of Legendre's theorem: a fraction
  close enough to `ξ` is a Stern–Brocot ancestor of `ξ`.

## Lesson for general BH

- **A good rational approximation is a shared vertex for free.** For lattice-boundary
  hosts, the descent systems of any two cells around a direction agree on every
  lattice point that approximates the direction well enough in both frames.
  - Such a point becomes a common ray without any synchronization between the frames,
    by a Euclid path on its coordinate vector.
  - The threshold is polynomial in the height, so very well approximable directions
    are never an obstruction.
- **Where the difficulty is.** The Serret-type gate sits at directions of exponent at
  most `m`. These include:
  - the generic directions, whose diagonal-flow orbits in the space of lattices
    return to compact sets infinitely often;
  - the badly approximable directions, whose orbits are bounded (Dani's
    correspondence, recalled);
  - singular directions of moderate exponent, whose orbits diverge.
