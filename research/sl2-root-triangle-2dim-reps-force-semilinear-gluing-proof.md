---
rg: 2
id: sl2-root-triangle-2dim-reps-force-semilinear-gluing-proof
kind: route
title: Two-dimensional injective representations of SL_2 over a field of characteristic 2 are field embeddings up to conjugation, and conjugations rescale root parameters
target: sl2-root-triangle-2dim-reps-force-semilinear-gluing
requires: [kazhdan-hyperbolic-sl2-root-triangles]
---

WLOG `K` is algebraically closed.

**0. Nontrivial means vertex-injective.** The vertex groups are simple, so `ρ|_{A_i}` is trivial or
injective.
- If `ρ|_{A_1}` is trivial, then `E_12` and `E_13` map trivially.
- `A_2 = <E_12, E_23>` then maps onto the image of the abelian group `E_23`. That image is a quotient of
  the simple group `A_2`, so it is trivial. `A_3` is likewise trivial, and `ρ` is trivial.
- The same argument starting from any vertex applies.

**1. Characteristic ≠ 2.** Let `A = SL_2(k)` and `U = u(k)`. `U` is a commuting set of involutions, so it
is diagonalizable, and `ρ(U)` is a sum of characters `ψ_a(u(x)) = χ(ax)`.
- A nontrivial character must occur, since otherwise `ker ρ` contains the normal closure of `U`, which is
  `A`.
- `diag(t, t^{-1})` carries `ψ_a` to `ψ_{at^{±2}}`, and squaring is onto `k^*`. So all `q - 1 >= 7`
  nontrivial characters occur, and `dim >= 7 > 2`.

So `ρ` would be trivial.

**2. Characteristic 2: injective `ρ: SL_2(k) -> GL_2(K)` is a field embedding up to conjugation.** The image
is perfect, so it lies in `SL_2(K)`. The same argument applies to `SL_2(F)`.
- **Fixed lines.** A nontrivial element of `ρ(u(k))` has order 2, hence `(g-1)^2 = 0`, and it fixes a
  unique line. Commuting ones fix the same line `L_+`; likewise `ρ(v(k))` fixes `L_-`. If `L_+ = L_-`,
  the image of `<u(k), v(k)> = SL_2(k)` would fix a line and be solvable. So, after conjugating,
  `ρ(u(x)) = u(α(x))` and `ρ(v(x)) = v(β(x))`, with `α, β` additive and injective.
- **Normalization.** `u(a)v(b)u(a) = [[1+ab, a^2 b],[b, 1+ab]]` and
  `v(b)u(a)v(b) = [[1+ab, a],[ab^2, 1+ab]]`. In `SL_2(k)`, `u(1)v(1)u(1) = v(1)u(1)v(1)`. So
  `a = α(1)`, `b = β(1)` satisfy `a^2 b = a`, that is `ab = 1`. Conjugating by `diag(t, t^{-1})` with
  `t^2 = 1/a` gives `α(1) = β(1) = 1`, and then `ρ(w) = w = [[0,1],[1,0]]`.
- **`β = α`.** `w u(x) w = v(x)` gives `v(α(x)) = ρ(v(x)) = v(β(x))`.
- **Inverses.** For `x ∈ k^*`, `w·u(x)v(1/x)u(x) = diag(1/x, x)`, which normalizes `u(k)` and `v(k)`. Its
  image normalizes `u(α(k))` and `v(α(k))`, so it lies in both Borel subgroups and is diagonal. The image
  is `w·[[1+ab, a^2b],[b, 1+ab]] = [[b, 1+ab],[1+ab, a^2b]]` with `a = α(x)`, `b = α(1/x)`. So `ab = 1`,
  that is `α(1/x) = α(x)^{-1}`.
- **`α` is a ring embedding (Hua's identity).** For `x, y ≠ 0` with `xy ≠ 1`, in characteristic 2,
  `x^2 y = x + (x^{-1} + (y^{-1} + x)^{-1})^{-1}`: indeed `(y^{-1}+x)^{-1} = y/(1+xy)`, then
  `x^{-1} + y/(1+xy) = 1/(x(1+xy))`, and `x + x(1+xy) = x^2 y`. Since `α` preserves sums and inverses,
  `α(x^2 y) = α(x)^2 α(y)`. The case `xy = 1` follows from `α(1/x) = α(x)^{-1}`.
  - With `y = 1`, `α(x^2) = α(x)^2`.
  - Every element of `k` is a square, so `α(zy) = α(z)α(y)` for all `z, y`.

So `ρ(g) = c·σ(g)·c^{-1}` for a field embedding `σ = α` applied entrywise.

**3. Edge consistency forces semilinear twists.** Write the embedding of `E_e` into `A_i` as
`ι_i(x) = r_i(c_i α_i(x))`, with `r_i ∈ {u, v}` and `c_i ∈ {1, s}` from the table, and `ρ|_{A_i} = conj_{g_i} ∘ σ_i`.
- Then `ρ(ι_i(x)) = g_i r_i(σ_i(c_i α_i(x))) g_i^{-1}`, and this must equal `ρ(ι_j(x))`.
- `h = g_j^{-1} g_i` carries a root subgroup of `r_i`-type onto one of `r_j`-type, so it maps fixed line
  to fixed line. It is therefore a Borel element, possibly times `w`, and acts on parameters by
  `y ↦ μ y` for one `μ ∈ K^*`.
- Hence `σ_j(c_j) σ_j(α_j(x)) = μ σ_i(c_i) σ_i(α_i(x))` for all `x`.
- Put `x' = α_i(x)` and `λ = μ σ_i(c_i)/σ_j(c_j)`. Then `σ_j(φ_e(x')) = λ σ_i(x')`, and `x' = 1` gives
  `λ ∈ σ_j(k)`.
- `σ_i(k)` and `σ_j(k)` are both the unique subfield `F_q ⊂ K`. So `φ_e = σ_j^{-1} ∘ (λ·) ∘ σ_i` on `k`:
  a Frobenius power followed by a scalar in `k^*`, which is semilinear.

∎
