---
rg: 2
id: renormalizable-thompson-elements-are-odometer-codes-proof
kind: route
title: Tower levels are a brick code, the digit-shift map reads off the odometer, and the renormalization multiplies drifts by m
target: renormalizable-thompson-elements-are-odometer-codes
requires:
  - renormalizable-thompson-elements-give-baumslag-solitar
  - bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets
---

Brick-local maps are closed under composition and inversion: refine to a common
brick partition, as for products in `kV`.

**Item 1.**
- (⇒) Put `e_i = T^i φ^{-1}: X -> T^i A`.
  - Each `e_i` is brick-local, and the images partition `X` by the tower
    condition.
  - `T e_i = e_(i+1)` for `i < m-1`.
  - `φ T^m φ^{-1} = T` gives `T^m φ^{-1} = φ^{-1} T`, i.e. `T e_(m-1) = e_0 T`.
- (⇐) Put `A = e_0 X` and `φ = e_0^{-1}`.
  - Then `T^i A = e_i X` for `i < m`, which partition `X`.
  - `T^m A = T e_(m-1) X = e_0 T X = A`, since `T` is onto.
  - `T^m e_0 = T e_(m-1) = e_0 T`, which is `φ T^m φ^{-1} = T`.
  - `φ` is brick-local.

**Item 2.**
- **Continuity.** `digit` is locally constant and `S` is brick-local, so each
  digit of `π` is locally constant. Hence `π` is continuous.
- **Fixed set.** Let `K = ∩_d e_(m-1)^d X`. Since `e_(m-1)` is injective,
  `e_(m-1) K = K`.
- **Points of K.** For `x ∈ K` write `x = e_(m-1) y` with `y ∈ K`. Then
  `T x = e_0 T y`. Iterating gives `T x ∈ ∩_d e_0^d X`, so `π(Tx) = 0`, while
  `π(x) = −1` (all digits `m-1`).
- **Other points.** Any other `x` is `e_(m-1)^d e_i y` with `d >= 0` and `i < m-1`.
  Then `T x = e_0^d e_(i+1) y`. The digits change from `(m-1)^d i` to `0^d (i+1)`
  and the rest is unchanged, which is `π(Tx) = π(x) + 1`.
- **Surjectivity.** The image of `π` is closed and invariant under `+1`, so it is
  all of `Z_m`.

**Item 3.**
- **(a)** If `T^p x = x` with `p >= 1`, then `π(x) + p = π(x)` in `Z_m`, which is
  impossible.
- **(b)** Let `μ` be `T`-invariant.
  - The tower levels have equal measure, so `μ_A = m μ|_A` is a probability
    measure, and it is `T^m|_A`-invariant.
  - Put `ν = φ_* μ_A`. It is `T`-invariant, because `φ T^m φ^{-1} = T`.
  - The exponent cocycle satisfies `δ_(gh)(x) = δ_g(hx) + δ_h(x)`. Hence
    `δ_T(φ a) = δ_φ(T^m a) + δ_(T^m)(a) − δ_φ(a)`.
  - Integrate against `μ_A`. The `δ_φ` terms cancel by invariance, so
    `∫ δ_T dν = ∫_A δ_(T^m) dμ_A`.
  - That equals `m Σ_(i<m) ∫_(T^i A) δ_T dμ = m ∫ δ_T dμ`.
  - So the set of drifts of invariant measures is invariant under multiplication by
    `m`. It is bounded, since `|δ_T| <= L(T)`, so it is `{0}`.
- **(c)**
  - From `T e_i = e_(i+1)`, `e_i = T^i e_0`, and `T^m e_0 = T e_(m-1) = e_0 T`.
    Hence `T^m e_i = T^i T^m e_0 = e_i T`.
  - Induction on the word length gives `T^(m^j) e_w = e_w T`.
  - The maps `e_w` are composites of `j` brick-local maps, so their table lengths
    are `O(j)`.

**Item 4.**
- **The code is standard.**
  - The images are two bricks `P = ∏[a_j]` and `Q = ∏[b_j]` with `P ⊔ Q = C^k`.
  - Pick a coordinate `j*` with `[a_(j*)] ∩ [b_(j*)] = ∅`.
  - If `a_j != ε` for some `j != j*`, take a point that lies in `[a_(j*)]` at `j*`
    and outside `[a_j]` at `j`. It is in neither brick.
  - So `a_j = b_j = ε` for `j != j*`, and `[a_(j*)] ⊔ [b_(j*)] = C`, which forces
    `{a_(j*), b_(j*)} = {0, 1}`.
- **Its odometer.**
  - Off `K`, the recursion forces `T(1^d 0 w, r) = (0^d 1 w, r)` in coordinate
    `j*`.
  - Continuity at `K = {1^∞} × C^(k-1)` forces `T(1^∞, r) = (0^∞, r)`.
  - So `T = τ × id`, which needs prefixes of every length and has no finite table. ∎

**Remark (full-shift full group).** An element `g` of the topological full group of
the full shift acts as `g(x) = σ^(c(x)) x`, so it fixes the two constant
configurations. By item 3(a) no such element, and no conjugate of one, is
renormalizable.
