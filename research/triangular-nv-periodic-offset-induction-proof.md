---
rg: 2
id: triangular-nv-periodic-offset-induction-proof
kind: route
title: Induct on the flag, using a periodic base point and the fibre return map, and read the nonzero offset from the base or from the fibre
target: triangular-subgroups-of-nv-contain-no-heisenberg-or-sl3z
requires:
  - infinite-order-elements-of-v-have-hyperbolic-periodic-points
  - heisenberg-in-nv-forces-drift-free-central-element
---

Write `p = (y, z)` with `y = π_{n−1}(p) ∈ C^{n−1}` and `z ∈ C`. For `g ∈ nV`,
the offset `s_g(p) ∈ Z^n` is well defined and satisfies the cocycle identity
(`heisenberg-in-nv-forces-drift-free-central-element`).

**Step 0: base and fibre maps.** Let `g ∈ T_n` with `n >= 2`.

- *Base map.* Since `g` maps `π_{n−1}`-fibres into `π_{n−1}`-fibres, there is a
  map `ḡ : C^{n−1} → C^{n−1}` with `π_{n−1} g = ḡ π_{n−1}`. The same holds for
  `g^-1`, and the two base maps are mutually inverse, so `ḡ` is a bijection.
- *Offsets on a brick.* Let `B = u_1C × ⋯ × u_nC` be a brick of a domain
  partition of `g`, on which `g` sends `(u_1w_1, …, u_nw_n)` to
  `(v_1w_1, …, v_nw_n)`.
  - On `π_{n−1}(B)`, `ḡ` is the prefix replacement `u_i → v_i` for `i < n`. The
    projections of the finitely many bricks cover `C^{n−1}`, and on overlaps
    they define the same map `ḡ`. After refining to a common dyadic partition,
    `ḡ` is a piecewise prefix replacement bijection, so `ḡ ∈ (n−1)V`.
  - Its offset satisfies `s_ḡ(y) = (s_g(y, z)_1, …, s_g(y, z)_{n−1})` for every
    `z`.
  - `ḡ ∈ T_{n−1}`, because `π_i` factors through `π_{n−1}` for `i < n−1`.
- *Fibre maps.* For each `y`, `g` restricts to a bijection
  `λ_y : C → C` with `g(y, z) = (ḡ(y), λ_y(z))`. On `u_nC`, for `y ∈ π_{n−1}(B)`,
  it is `u_n → v_n`. So `λ_y ∈ V` and `s_{λ_y}(z) = s_g(y, z)_n`.
  - `λ_y` is determined by the set `J(y)` of bricks whose projection contains
    `y`, so `y ↦ λ_y` takes finitely many values.
- *Functoriality.* `(gh)‾ = ḡ h̄`, and `λ^{gh}_y = λ^g_{h̄(y)} ∘ λ^h_y`.

**Step 1: every element has a periodic point.** This is trivial for
finite-order `g`, and follows from Step 2 for infinite-order `g`.

**Step 2: induction on n.**

- *Case `n = 1`.* Here `T_1 = V`, and the statement is
  `infinite-order-elements-of-v-have-hyperbolic-periodic-points`: the slope
  `2^{|u|−|v|}` of `g^k` at `p` differs from `1` iff `s_{g^k}(p) ≠ 0`.
- *Case `n >= 2`.* Assume the statement for `T_{n−1}`, and let `g ∈ T_n` have
  infinite order, with `h = ḡ ∈ T_{n−1}`.

*Case A: `h` has infinite order.*

1. By induction there are `y_0` and `a >= 1` with `h^a(y_0) = y_0` and
   `s_{h^a}(y_0) ≠ 0`.
2. By functoriality, `g^a` maps the fibre over `y_0` to itself by
   `μ = λ^{g^a}_{y_0} ∈ V`. By Step 1 for `V`, `μ` has a periodic point `z_0`, of
   period `b`.
3. Put `P = (y_0, z_0)`, so that `g^{ab}(P) = P`. By Step 0 and the cocycle
   identity along the `h^a`-fixed point `y_0`, the first `n−1` coordinates of
   `s_{g^{ab}}(P)` equal `s_{h^{ab}}(y_0) = b·s_{h^a}(y_0) ≠ 0`.

*Case B: `h` has finite order `r`.*

1. `g^r ∈ T_n` has base map `id` and infinite order. Its fibre maps
   `λ'_y = λ^{g^r}_y` take finitely many values by Step 0, and
   `(g^r)^m(y, z) = (y, (λ'_y)^m(z))`.
2. If every `λ'_y` had finite order, the least common multiple `L` of these
   orders would give `g^{rL} = id`, which is impossible. So some `λ'_{y_0}` has
   infinite order.
3. By the case `n = 1`, there are `z_0` and `b >= 1` with
   `(λ'_{y_0})^b(z_0) = z_0` and `s_{(λ'_{y_0})^b}(z_0) ≠ 0`.
4. Put `P = (y_0, z_0)`. Then `g^{rb}(P) = P`, and by Step 0 the last coordinate
   of `s_{g^{rb}}(P)` is `s_{(λ'_{y_0})^b}(z_0) ≠ 0`.

*Common conclusion.* In both cases `g^N(P) = P` and `s_{g^N}(P) ≠ 0` for some
`N`. Let `k` be the exact period of `P`. Then `k | N`, and the cocycle identity
gives `s_{g^N}(P) = (N/k)·s_{g^k}(P)`, so `s_{g^k}(P) ≠ 0`. This proves item 1.

**Item 2.**

- The measure `ν = (1/k) Σ_{j<k} δ_{g^j P}` is `g`-invariant.
- Its drift is `ρ_ν(g) = (1/k) Σ_{j<k} s_g(g^j P) = (1/k) s_{g^k}(P) ≠ 0`.
- Undistortion follows from item 1 of the imported theorem.

**Item 3.** Nontrivial central powers of the three kinds of element are again
elements of the same kind:

- *Heisenberg.* If `c = [a, b]` is central in `H_3(Z) ≤ nV`, then for `m ≠ 0` the
  element `c^m = [a^m, b]` commutes with `a^m` and with `b`, and has infinite
  order.
- *Baumslag–Solitar.* `t x^m t^-1 = (x^m)^k`.
- *Root elements.* In `SL_d(Z)` with `d >= 3`, pick `k ∉ {i, j}`. Then
  `e_ij^m = [e_ik^m, e_kj]` commutes with `e_ik^m` and `e_kj`. `GL_d(Z)` contains
  `SL_d(Z)`.

Conjugating the whole subgroup by `f^-1` preserves these relations. So if such
an element lay in `f T_n f^-1`, its `f^-1`-conjugate would be an infinite-order
element of `T_n` that is drift-free by items 2 and 3 of
`heisenberg-in-nv-forces-drift-free-central-element`. That contradicts item 2
here. ∎
