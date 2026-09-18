---
rg: 2
id: metallic-wang-product-minimality-and-row-faults-proof
kind: route
title: Approach a horizontal partition line from both sides to get a two-row fault in each metallic mean Wang shift, and use disjoint eigenvalues to make the product minimal
target: metallic-wang-shift-product-is-minimal-with-split-differences
requires: []
---

The notation is that of the target. `{z} = z - ⌊z⌋`.

## Imported (verbatim, S. Labbé, arXiv:2403.03197v3)

- **[L1] Theorem 1.1 ([Lab25a]).** "For every integer n≥ 1, (i) the metallic mean Wang shift Ωn
  is self-similar, aperiodic and minimal, (ii) the inflation factor of the self-similarity of Ωn is
  the n-th metallic mean, that is, the positive root of x2−nx− 1."
- **[L2] Section 3.** "Let ΩT ⊂ {0,...,m − 1}Z2 denote the set of all valid configurations with
  respect to T. Together with the shift action σ of Z2, ΩT is a subshift that we call a Wang shift.
  Furthermore, ΩT is a subshift of finite type (SFT) of the form (3.2) since ΩT is the subshift
  defined from the finite set of forbidden patterns made of all horizontal and vertical dominoes of
  two tiles that do not share an edge of the same color."
- **[L3] Definition of `Λ_n` and `Tile_n` (Section 2).** "Let Λn : [0, 1)2→ Z3 be defined as
  Λn(x,y) = (⌊y−β−1 + 1⌋, ⌊β−1x + y−β−1 + 1⌋, ⌊βx + y−β−1 + 1⌋) where β is the nth metallic mean
  ... For every (x,y) ∈ R2, let Tilen(x,y) = [Λn({x},{y}), Λn({y},{x}), Λn({x−β−1},{y}),
  Λn({y−β−1},{x})] be a Wang tile". (The column vector is written as a row, and the four entries
  are placed on the tile's sides.) The proof of Theorem C says which side is which: "the right color of the tile c(x,y)(i,j) is
  Λn({x+iβ−1},{y+jβ−1}) ... the top color of the tile c(x,y)(i,j) is Λn({y+jβ−1},{x+iβ−1})".
- **[L4] Theorem C.** "For every integer n≥ 1 and every (x,y) ∈ [0, 1)2, the configuration
  c(x,y) : Z2 → Tn, (i,j) ↦ Tilen(x+iβ−1, y+jβ−1) is a valid tiling of the plane by the set of
  metallic mean Wang tiles Tn."
- **[L5] Theorem D.** "The map Φn : Ωn → T2 ... is a factor map, that is, it is continuous, onto
  and commutes the shift Z2 ↷σ Ωn with the toral Z2-rotation Z2 ↷Rn T2 by the equation
  Φn◦σk = Rkn◦Φn for every k∈ Z2 where Rn : Z2 × T2 → T2, (k,x) ↦ Rkn(x) := x + βk and
  β = (n+√(n2+4))/2 is the nth metallic mean".
- **[L6] Theorem F (ii).** "the factor map Φn : Ωn → T2 is almost one-to-one and its set of fiber
  cardinalities is {1, 2, 8}". From Section 3.1: "the factor map θ is almost one-to-one if
  {y∈ Y : card(θ−1(y)) = 1} is a Gδ-dense set in Y".

Here `T^2 = R^2/Z^2`, the torus of the fractional parts in [L3]–[L5].

**Standard facts, also imported.**
- **Kronecker.** A subgroup `H` of `T^d = R^d/Z^d` is dense iff no nonzero character
  `z ↦ exp(2πi⟨a, z⟩)`, with `a ∈ Z^d`, is trivial on `H`.
- `1`, `sqrt 2` and `sqrt 5` are linearly independent over `Q`.

## 1. Part 1: finite type, freeness and minimality of `X`

- **Finite type.** `Ω_1` and `Ω_2` are SFTs by [L2], so `X = Ω_1 × Ω_2` is an SFT on the alphabet
  `T_1 × T_2`. Its forbidden patterns are the dominoes whose first or second coordinates are
  forbidden. `X` is nonempty by [L4].
- **Freeness.** If `k ≠ 0` fixes `(w_1, w_2)`, it fixes `w_1 ∈ Ω_1`. Then `w_1` is periodic,
  which contradicts aperiodicity [L1(i)].

### Minimality of the product rotation

`R = R_1 × R_2` acts on `T^4` by `k.(z_1, z_2) = (z_1 + β_1 k, z_2 + β_2 k)`, so orbits are cosets
of `H = {(β_1 k_1, β_1 k_2, β_2 k_1, β_2 k_2) : k ∈ Z^2}`.
- Let a character `(a, b, c, d) ∈ Z^4` be trivial on `H`. Taking `k = e_1` and `k = e_2` gives
  `a β_1 + c β_2 ∈ Z` and `b β_1 + d β_2 ∈ Z`.
- Write `p + q β_1 + r β_2 = (p + q/2 + r) + (q/2) sqrt 5 + r sqrt 2` for rationals `p, q, r`.
  This is `0` only when `p = q = r = 0`. So `a = b = c = d = 0`.
- By Kronecker, `H` is dense. Every orbit `z + H` is dense, so `R` is minimal.

### Lemma 1 (product of almost one-to-one extensions)

For `i = 1, 2`, let `(Ω_i, Z^2)` be minimal, and let `Φ_i : Ω_i -> Z_i` be continuous,
equivariant and almost one-to-one. If `Z_1 × Z_2` is minimal, then `Ω_1 × Ω_2` is minimal.

*Proof.*
1. Let `W_i = {w ∈ Ω_i : Φ_i^(-1)(Φ_i(w)) = {w}}`. It is nonempty, since singleton fibres
   exist (a dense `G_δ` is nonempty).
2. `W_i` is invariant. By equivariance, `Φ_i^(-1)(k.z) = k.Φ_i^(-1)(z)` for each `k`, because each
   `k` acts bijectively.
3. A nonempty invariant subset of a minimal system contains a full orbit, so it is dense.
   Hence `W_1 × W_2` is dense in `Ω_1 × Ω_2`.
4. Let `M ⊆ Ω_1 × Ω_2` be nonempty, closed and invariant. Then `(Φ_1 × Φ_2)(M)` is compact,
   nonempty and invariant, so it is all of `Z_1 × Z_2`.
5. For `(w_1, w_2) ∈ W_1 × W_2`, some point of `M` maps to `(Φ_1 w_1, Φ_2 w_2)`. The fibre over
   that point is `{(w_1, w_2)}`, so `(w_1, w_2) ∈ M`.
6. So `M ⊇ W_1 × W_2` is dense and closed, and `M = Ω_1 × Ω_2`. ∎

Apply Lemma 1 with `Φ_i` from [L5], using [L1(i)] and [L6]. Then `X` is minimal. The choice of
convention for the shift action (`σ^k` or `σ^(-k)`) does not affect invariance, minimality or
freeness.

## 2. Part 2: a two-row fault in `Ω_n`

Fix `n` and write `β = β_n`, so `0 < β^(-1) < 1`. Fix `x ∈ [0, 1) \ Q(β)`, and for
`0 <= t < β^(-1)` put:
- `y(t) = 1 - t` for `t > 0`, and `y(0) = 0`;
- `x_i = x + iβ^(-1)`.

Let `c = c_(x,0)` and `c_t = c_(x, 1-t)` for `t > 0`. Both lie in `Ω_n` by [L4].

The tile `c_(x,y)(i, j)` is a function of four quantities: `{x_i}`, `{x_(i-1)}`,
`{y + jβ^(-1)}` and `{y + (j-1)β^(-1)}`. Each of its twelve integer entries is `⌊λ⌋` for an
affine form `λ` of these quantities, given by [L3]:
- right, `Λ_n({x_i}, {y_j})`;
- top, `Λ_n({y_j}, {x_i})`;
- left, `Λ_n({x_(i-1)}, {y_j})`;
- bottom, `Λ_n({y_(j-1)}, {x_i})`;

where `y_j = y + jβ^(-1)`.

**(a) Outside rows 0 and 1 nothing changes for small `t`.** Let `j ∉ {0, 1}`.
- `jβ^(-1) ∉ Z` and `(j-1)β^(-1) ∉ Z`. So `y ↦ {y + jβ^(-1)}` and `y ↦ {y + (j-1)β^(-1)}` are
  continuous at `y ≡ 0` on `R/Z`. At `y = 0` their values `{jβ^(-1)}` and `{(j-1)β^(-1)}` lie
  in `Q(β)`.
- `{x_i}` and `{x_(i-1)}` do not lie in `Q(β)`, and do not depend on `y`.
- Every form containing `{x_i}` or `{x_(i-1)}` does so with a coefficient in `{1, β^(-1), β}`, and
  its other terms lie in `Q(β)`. So at `y = 0` it is not in `Q(β)`, and in particular not an
  integer.
- The only forms without an `x`-term are the first entries of right and left,
  `{y_j} - β^(-1) + 1`. At `y = 0` this equals `(j - 1)β^(-1)` plus an integer, which is an integer
  only if `j = 1`.
- So at `y = 0`, for `j ∉ {0, 1}`, all twelve forms are non-integers and depend continuously on
  `y`. Their floors are constant near `y = 0`, and `c_t(i, j) = c(i, j)` for all `t` below some
  `t_(i,j) > 0`.

**(b) Row 1 changes everywhere.** The first entry of the right label of `c_(x,y)(i, 1)` is
`⌊{y + β^(-1)} - β^(-1) + 1⌋`.
- For `y = 0` it is `⌊β^(-1) - β^(-1) + 1⌋ = 1`.
- For `y = 1 - t`, `0 < t < β^(-1)`, we have `{1 - t + β^(-1)} = β^(-1) - t`, and the entry is
  `⌊1 - t⌋ = 0`.

**(c) The pair.** `Ω_n` is compact, so `c_(t_k)` converges to some `c' ∈ Ω_n` along a sequence
`t_k -> 0`. Each coordinate is eventually constant, since the alphabet is finite. By (a),
`c'(i, j) = c(i, j)` for `j ∉ {0, 1}`. By (b), `c'(i, 1) ≠ c(i, 1)` for every `i`. So
`Z × {1} ⊆ Δ(c, c') ⊆ Z × {0, 1}`. ∎

**Numerical check.** `experiments/metallic-wang-product-2026-09-17/row_fault_check.py` evaluates
`c_(x,0)` and `c_(x,1-10^(-30))` on `[-40, 40]^2` with `x = 1/sqrt 3`, for `n = 1, 2, 3`, at 60
digits. For all three it reports:
- differing rows `{0, 1}`;
- every tile of row 1 differs;
- the Wang matching conditions hold on the window.

## 3. Part 3: split differences

Let `(c_i, c_i')` be the pair of part 2 in `Ω_i`. Fix `m`, put `g = (0, m + 2)` and
`(g.w)(p) = w(p - g)`, so `Δ(g.w, g.w') = Δ(w, w') + g`. Let `u = (c_1, g.c_2)` and
`v = (c_1', g.c_2')` in `X`. Then

    Δ(u, v) = Δ(c_1, c_1') ∪ (Δ(c_2, c_2') + g) =: Δ_1 ⊔ Δ_2,

with:
- `∅ ≠ Δ_1 ⊆ Z × {0, 1}`;
- `∅ ≠ Δ_2 ⊆ Z × {m + 2, m + 3}`;
- `ℓ^1` distance `d(Δ_1, Δ_2) >= m + 1 > m`.

So `Δ(u, v)` is not `m`-connected. ∎

## Remarks

- Within one `Ω_n` the faults at rows `{0,1}` come from the horizontal partition lines `y = 0` and
  `y = β^(-1)` of [L3]. Two such lines are hit by one orbit only in adjacent rows. So part 3 is not
  claimed for `Ω_n` alone.
- `Ω_1 × Ω_4` would not work, because `β_4 = 2 + sqrt 5` and `1, β_1, β_4` are dependent. A
  self-product `Ω_n × Ω_n` is not minimal either, since its diagonal is invariant and closed.
