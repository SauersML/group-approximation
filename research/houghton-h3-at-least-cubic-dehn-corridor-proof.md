---
rg: 2
id: houghton-h3-at-least-cubic-dehn-corridor-proof
kind: route
title: Y-corridors in the ascending HNN extension H_3 = H_2 *_φ force cubic area on [Y^m X^m Y^-m, α]
target: houghton-group-h3-has-at-least-cubic-dehn-function
requires: []
artifacts:
  - experiments/houghton-heisenberg-2026-09-17/check_forced.py
  - experiments/houghton-heisenberg-2026-09-17/check_forced.out
  - experiments/houghton-heisenberg-2026-09-17/corridor_lb.py
  - experiments/houghton-heisenberg-2026-09-17/corridor_lb_ga.out
  - experiments/houghton-heisenberg-2026-09-17/sanity.py
  - experiments/houghton-heisenberg-2026-09-17/sanity.out
---

**Theorem.** `x^3 ≼ δ_(H_3)(x)`. More precisely, in the finite presentation
`P` of Step 1, the words `w_m` (`m >= 2`) of Step 3 are null-homotopic, have
length `6m + 2`, and satisfy `Area_P(w_m) >= m^2 (m - 1)`.

The only imported input is that `H_3` is finitely presented:

> "Corollary B. For n ≥ 2, H_n is of type FP_(n−1) but not FP_n, it is finitely
> presented for n ≥ 3."
> (S. R. Lee, *Geometry of Houghton's groups*, arXiv:1212.0257, Corollary B;
> originally K. S. Brown, *Finiteness properties of groups*, J. Pure Appl.
> Algebra 44 (1987).)

Lee's explicit presentation (Theorem C / Theorem 2.14 there) is **not** used.
Its relator `r'_5` is garbled in the arXiv text layer, and only the form
`α^(g_i^-1) = α^(g_j^-1)` holds as permutations. The proof below replaces it
with a presentation derived from finite presentability.

## Conventions

- Points of ray `r` are `(r, p)` with `r ∈ {1, 2, 3}` and `p >= 1`.
- Permutations act on the right, so a word is applied letter by letter from
  left to right, and `h^u = u^(-1) h u`.
- `λ_(a,b)` maps `(a, p) ↦ (a, p-1)` for `p >= 2`, `(a, 1) ↦ (b, 1)` and
  `(b, p) ↦ (b, p+1)`, and fixes the third ray.
- `X = λ_(1,2)`, `Y = λ_(1,3)` and `α = ((1,1),(1,2))`.
- `B = <X, α> ≤ H_3`. Every element of `B` fixes ray 3 pointwise.
- `τ : H_3 → Z` is the eventual translation on ray 3: every `h ∈ H_3` satisfies
  `(3, p) h = (3, p + τ(h))` for all large `p`. It is a homomorphism with
  `τ(Y) = 1` and `τ(X) = τ(α) = 0`, so `τ(word)` is its `Y`-exponent sum.
- The line `L = ray 2 ∪ ray 1` is ordered
  `… < (2,2) < (2,1) < (1,1) < (1,2) < …`.
- For `h ∈ B`, `h` permutes `L`. Set
  `inv(h) = #{(y, y') : y < y' in L, y h > y' h}`. This is finite because `h`
  agrees with an order-preserving shift of `L` outside a finite set.

## Step 1. A finite presentation with HNN shape

**1a. Two identities in `H_3`.** `Y X Y^(-1) = α X` and
`Y α Y^(-1) = X α X^(-1)`. Both sides are explicit permutations; checking
them on the points `(r, p)` with `p <= 3` suffices, since both sides
translate uniformly beyond that. They are also machine-checked (`check_forced.py`,
first line of `check_forced.out`). So `φ(h) = Y h Y^(-1)` maps `B` into `B`,
with `φ(X) = αX` and `φ(α) = XαX^(-1)`.

**1b. `H_3` is the ascending HNN extension `B *_φ`.** First, `X, Y, α`
generate `H_3`:

- `α^(X^k)` swaps `(1,1)X^k` and `(1,2)X^k`. These points are adjacent in the
  line `L`, and as `k` ranges over `Z` every adjacent pair of `L` arises.
- The same holds for `α^(Y^k)` and the line ray 3 ∪ ray 1.
- The union of the two adjacency graphs is connected on all points. Adjacent
  transpositions along a connected graph generate the whole finitary symmetric
  group, so `<X, Y, α>` contains every finitary permutation.
- The translation vectors `(-1, 1, 0)` of `X` and `(-1, 0, 1)` of `Y` span the
  sum-zero lattice of `Z^3`. So any `h ∈ H_3` differs from some word in `X, Y`
  by a finitary permutation.

Let `G* = <B, t | t b t^(-1) = φ(b), b ∈ B>`, and let `π : G* → H_3` be the
identity on `B` with `t ↦ Y`. Then `π` is well defined by 1a and onto.

Because `t B t^(-1) ⊆ B`, every element of `G*` can be written `t^(-a) b t^c`
with `a, c >= 0` and `b ∈ B`. To see this, push each `t` to the right with
`t b = φ(b) t`, and each `t^(-1)` to the left with `b t^(-1) = t^(-1) φ(b)`.

Suppose `π(t^(-a) b t^c) = 1`. Then `c - a = τ(1) = 0`, so
`Y^(-a) b Y^a = 1` in `H_3`. Hence `b = 1` in `H_3`, and so `b = 1` in the
subgroup `B`. So `π` is injective.

**1c. The presentation.** Let `R_B` be the set of all words in `X^(±1)`,
`α^(±1)` that are trivial in `B`. Then
`H_3 = <X, α, Y | R_B, ρ_X, ρ_α>`, where

- `ρ_X = Y X Y^(-1) X^(-1) α^(-1)`,
- `ρ_α = Y α Y^(-1) X α^(-1) X^(-1)`.

This is the standard presentation of the HNN extension `G*`. The associated
map is given on the generators `X, α` of `B`.

`H_3` is finitely presented (Corollary B above). By B. H. Neumann's theorem,
every presentation of a finitely presented group on finitely many generators
has a finite subset of relators that already presents the group. So there is a
finite `R_0 ⊆ R_B` such that

`P = <X, α, Y | R_0 ∪ {ρ_X, ρ_α}>`

presents `H_3`. Adding `ρ_X` and `ρ_α` to the finite subset does no harm.

**Shape of `P`.** Relators in `R_0` contain no `Y`-letter. Each of `ρ_X` and
`ρ_α` contains exactly one `Y` and one `Y^(-1)`. Cut at its two `Y`-letters,
each of these relators has two **sides**:

| relator | first side | second side |
|---|---|---|
| `ρ_X` | `X` | `X^(-1) α^(-1)` |
| `ρ_α` | `α` | `X α^(-1) X^(-1)` |

Every side contains at most one letter `α^(±1)`.

## Step 2. Corridors and the inversion bound

**2a. Inversions.**

- `inv` is subadditive on `B`. If `y < y'` is inverted by `gh` (right
  action), then either `g` inverts `(y, y')`, or `g` preserves it and `h`
  inverts `(yg, y'g)`. This gives an injection of the inversion set of `gh`
  into the disjoint union of the inversion sets of `g` and `h`.
- `inv(g^(-1)) = inv(g)`.
- `inv(X^(±1)) = 0`, because `X` shifts `L` by one step in an
  order-preserving way.
- `inv(α) = 1`, because `α` swaps the adjacent points `(1,1) < (1,2)`.

So a word `U` in `X^(±1)`, `α^(±1)` satisfies
`inv(Ū) <= #(letters α^(±1) in U)`.

**2b. Corridors (the standard `t`-corridor argument, written out).** Let `D`
be a van Kampen diagram over `P`
for a null-homotopic word `w`. Call a `Y`-edge of `D` a boundary `Y`-edge if
it lies on `∂D`.

Start at a boundary `Y`-edge `e`.

- If no 2-cell contains `e`, then `e` is a tree edge. It occurs twice on
  `∂D`, and the corridor is empty.
- Otherwise `e` lies on exactly one cell `c_1`, because its other side is the
  exterior. Then `c_1` is a `ρ`-cell, and `c_1` has exactly one other
  `Y`-edge `e_1 ≠ e`. (`e` cannot occur twice on `∂c_1`, since only one side
  of `e` is `c_1`.) Continue through `e_1`.

A cell has only two `Y`-edge occurrences, so no cell is visited twice. The
chain therefore stops at a boundary `Y`-edge `e' ≠ e`, and the chain
`c_1, …, c_ℓ` is the corridor from `e` to `e'`.

This pairs the boundary `Y`-letters of `w` by an involution without fixed
points. Distinct corridors share no cell.

*Orientation.* Take the plane orientation and read every cell boundary and
`∂D` counterclockwise. Let `γ` be the dual arc of the corridor: it runs from
the midpoint of `e` through `c_1, …, c_ℓ` to the midpoint of `e'`, crossing
each `e_k` once.

Consider a cell `c`, and let `T` be its counterclockwise boundary tangent. At
the edge where `γ` enters, `γ` points along the inward normal `n`, and `T`
points to the right of `n`. At the edge where `γ` leaves, `γ` points along
`-n`, and `T` points to the left of `γ`.

The counterclockwise label of `c` is a cyclic conjugate of `ρ^(±1)`, so it
reads one of its two `Y`-edges forward and the other backward.

- If `γ` enters through the forward edge, both `Y`-edges of `c` point to the
  right of `γ`.
- If `γ` enters through the backward edge, both point to the left of `γ`.

Consecutive cells share their `Y`-edge, so every `Y`-edge of the corridor
points to the same side of `γ`, say the right. The case of the left side is
symmetric.

Near the midpoint of a boundary edge lying on a cell, `D` is locally a
half-disc, so the same tangent rule applies to `∂D`:

- at `e`, `γ` points inward, so `∂D` reads `e` forward;
- at `e'`, `γ` points outward, so `∂D` reads `e'` backward.

So **paired boundary `Y`-letters have opposite exponents.**

*Sides.* In each cell, the two `Y`-edges cut the boundary into its two sides
(Step 1). The sides lying to the right of `γ` join the heads of the `Y`-edges.
Concatenated, they give a path in `D` from `head(e)` to `head(e')`, labelled
by a word in `X^(±1)`, `α^(±1)` that contains at most one letter `α^(±1)` per
cell. Likewise, the sides to the left give a path from `tail(e)` to
`tail(e')`.

**2c. The arc lemma.** Let the paired letters be positions `i < j` of `w`
(read as a linear word). Let `v_k` be the boundary vertex after letter `k`.

- If `w_i = Y` and `w_j = Y^(-1)`, then `head(e) = v_i` and
  `head(e') = v_(j-1)`.
- If `w_i = Y^(-1)` and `w_j = Y`, then `tail(e) = v_i` and
  `tail(e') = v_(j-1)`.

In either case one side of the corridor is a path in `D` from `v_i` to
`v_(j-1)` whose label `U` is a word in `X^(±1)`, `α^(±1)` with at most `ℓ`
letters `α^(±1)`. That is one per cell, by the shape of `P`. The boundary arc
`w(i, j) = w_(i+1) … w_(j-1)` runs between the same two vertices of the
simply connected `D`, so `w(i, j) = U` in `H_3`. Therefore:

- **(admissible)** `w(i, j) ∈ B`. In particular `w(i, j)` fixes ray 3
  pointwise, and `τ(w(i, j)) = 0`.
- **(cost)** `ℓ >= inv(w(i, j))`, by 2a.

Summing over corridors, which are cell-disjoint:

`Area_P(w) >= Σ_{paired (i, j)} inv(w(i, j))`,

and every pair `(i, j)` has opposite signs and is admissible.

## Step 3. The words `w_m` and the forced matching

Fix `m >= 2`, put `g = Y^m X^m Y^(-m)`, and let

`w_m = g^(-1) α^(-1) g α`, freely equal to `Y^m X^(-m) Y^(-m) α Y^m X^m Y^(-m) α`.

This word has length `6m + 2`. Its `Y`-letters form four blocks, in order of
appearance:

- `A = a_1 … a_m` (each `Y`),
- `B' = b_1 … b_m` (each `Y^(-1)`),
- `C = c_1 … c_m` (each `Y`),
- `D' = d_1 … d_m` (each `Y^(-1)`).

**Null-homotopy.** `g = (X^m)^(Y^(-m))`. `Y^m` sends `(1, p) ↦ (3, m + 1 - p)`
for `p <= m`, and `X^m` fixes ray 3. So `g` fixes `(1, 1), …, (1, m)`. Since
`m >= 2`, `g` commutes with `α = ((1,1),(1,2))`.

Two facts do the computations.

- **(F1)** `α^(Y^k)` swaps `(1,1)Y^k` and `(1,2)Y^k`. For `k >= 1`,
  `(1,1)Y^k = (3, k)`, so `α^(Y^k)` moves the ray-3 point `(3, k)`. For
  `k >= 2`, `α^(Y^k) = ((3, k-1), (3, k))`.
- **(F2)** `h_k = Y^k X^(-m) Y^(-k)` (`k >= 0`) fixes ray 3 pointwise, and
  `inv(h_k) = k m`.

*Proof of (F2).* Put `F = {(1,1), …, (1,k)}`. Then `h_k`:

- fixes `F`;
- sends `(1, p) ↦ (1, p + m)` for `p > k`;
- sends `(2, q) ↦ (2, q - m)` for `q > m`;
- sends `(2, q) ↦ (1, k + m + 1 - q)` for `q <= m`.

So on `L \ F` it is the order-preserving shift by `m` steps. The only
inverted pairs are `((2, q), f)` with `q <= m` and `f ∈ F`. Before `h_k`,
`(2, q) < f`. After it, `(2, q) h_k` lies on ray 1 at depth `> k`, above
`f = f h_k`. That makes `m k` pairs. On ray 3, `Y^k` shifts by `k`, `X^(-m)`
does nothing, and `Y^(-k)` shifts back. ∎

By Step 2, a van Kampen diagram for `w_m` pairs its `4m` `Y`-letters into
admissible pairs of opposite sign. Admissible means `τ(arc) = 0` and the arc
fixes ray 3. The `a` and `c` letters are `Y`, and the `b` and `d` letters are
`Y^(-1)`, so the opposite-sign pairs are exactly the four types below.

**(i) `a_i` with `b_j`.** The arc is `Y^(m-i) X^(-m) Y^(-(j-1))`, so
`τ = 0` forces `j = m + 1 - i`. Then the arc is `h_k` with `k = m - i`. It
is admissible, with cost `k m`.

**(ii) `a_i` with `d_j`.** The arc is
`Y^(m-i) X^(-m) Y^(-m) α Y^m X^m Y^(-(j-1))`. `τ = 0` forces
`j - 1 = m - i =: k`, with `0 <= k <= m - 1`. Then the arc is
`(X^(-m) α^(Y^m) X^m)^(Y^(-k))`.

- By (F1), `α^(Y^m) = ((3, m-1), (3, m))`.
- `X^(±m)` fixes ray 3, so conjugating by it leaves this transposition alone.
- So the arc moves exactly the points `z` with
  `z Y^k ∈ {(3, m-1), (3, m)}`. These include `z = (3, m - k)`, a ray-3
  point because `m - k >= 1`.

**Inadmissible for every `i`.**

**(iii) `b_j` with `c_i`.** The arc is `Y^(-(m-j)) α Y^(i-1)`. `τ = 0` forces
`i - 1 = m - j =: k`, and then the arc is `α^(Y^k)`. By (F1) it is
inadmissible for `k >= 1`. The only admissible pair is `b_m` with `c_1`
(arc `α`).

**(iv) `c_i` with `d_j`.** The arc is `Y^(m-i) X^m Y^(-(j-1))`. `τ = 0`
forces `j = m + 1 - i`, and then the arc is `h_(m-i)^(-1)`. It is
admissible, with cost `(m - i) m`.

**Forcing.** Each `a_i` must pair with a `Y^(-1)`-letter. By (ii) that
letter is not a `d`, so by (i) it is `b_(m+1-i)`. This uses up all of `B'`.
Each `c_i` must then pair with a `d`, and by (iv) that is `d_(m+1-i)`.

So the matching is unique, and admissibility alone forces it: planarity is
not used. Its cost is

`Σ_{i=1}^m (m-i) m + Σ_{i=1}^m (m-i) m = m^2 (m-1)`,

so by Step 2, `Area_P(w_m) >= m^2 (m - 1)`.

**Machine check.**

- `check_forced.py` recomputes, for `m = 2..8`, the admissible partner set
  and cost of every `a_i` and `c_i` by explicit permutation arithmetic
  (`check_forced.out`). It tests only the ray-3 condition, which is
  necessary for admissibility.
- The interval DP in `corridor_lb.py` searches all non-crossing admissible
  matchings, which relaxes the forced one. It returns exactly `m^2 (m-1)` for
  `m = 2..8` (`corridor_lb_ga.out`).

## Step 4. Conclusion

For `x >= 14`, let `m = ⌊(x - 2)/6⌋ >= 2`. Then

`δ_P(x) >= δ_P(6m+2) >= m^2 (m-1) >= c x^3`

for some `c > 0` and all large `x`. Dehn functions of any two finite
presentations of a group are `≃`-equivalent, so `x^3 ≼ δ_(H_3)(x)`. ∎

## Remarks

- **Mechanism.** `H_3` is an ascending HNN extension of `H_2 = B`, and every
  cell side of the associated map carries at most one unit of inversion cost.
  `H_2` is quadratically distorted in `H_3`:
  - `B`-length of `h_(m-1)`: at least `(m-1) m`, because every `α`-letter
    adds at most one inversion;
  - `H_3`-length: at most `3m`.

  The cubic area is the corridor consequence of that distortion.
- **Other `n`.** For `n >= 4`, the same argument with base `H_(n-1)`
  (stabilizer of one ray) needs `H_(n-1)` to be distorted in `H_n`. With a
  spare ray, the analogous elements look short in `H_(n-1)`. This was not
  proved here, and the method gives no bound beyond `x^2` for `n >= 4`.
