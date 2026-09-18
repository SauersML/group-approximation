---
rg: 2
id: q-x2-z-in-t-check-has-a-doubling-semiconjugacy-proof
kind: route
target: q-x2-z-in-t-check-has-a-doubling-semiconjugacy
requires: []
---

Direct proof. Notation as in the claim. Two standard facts are used.
- **(F1) Translation number.** A homeomorphism `f` of `R` commuting with `τ_L`
  (`L > 0`) has `ρ(f) = lim (f^n(x) - x)/n`, independent of `x`, with
  `|f^n(x) - x - nρ(f)| < L` for all `x, n`. Also `ρ(f^n) = nρ(f)`, and
  `ρ(fg) = ρ(f) + ρ(g)` for commuting `f, g`. `ρ` is invariant under conjugation
  by homeomorphisms commuting with a common translation. `ρ(f) = 0` iff `f` has a
  fixed point.
- **(F2) Rationality.** Every element of Thompson's `T` has rational rotation number
  (Ghys--Sergiescu, Comment. Math. Helv. 62 (1987)). So `ρ(T-bar) ⊆ Q`, and
  `ρ(δ^k f δ^-k) = 2^k ρ(f)` gives `ρ(T-bar_∞) ⊆ Q`.

**Step 1 (item 1).**
- `χ(D)` is a divisible subgroup of `Z`, so `D <= T-bar_∞`. Every `q in D`
  commutes with some `τ_(2^k)`, and any two elements of `D` commute with a common
  one. So `ρ|_D` is a homomorphism `D -> Q`.
- Write `t = g δ^j` with `g in T-bar_∞`. Conjugating by `g` preserves `ρ` (F1), and
  conjugating by `δ` doubles it. So `2ρ(q) = ρ(q^2) = ρ(t q t^-1) = 2^j ρ(q)`.
- **`ρ|_D` is not zero.** Suppose it is. Take `1 ≠ q in D`. It has a fixed point
  (F1), and `Fix(q)` is a proper closed set. At a boundary point `p` of `Fix(q)`,
  `q` is linear with slope `2^α`, `α ≠ 0`, on one side of `p`. Elements of `T-bar_∞`
  have locally finitely many breakpoints, and a slope `1` there would make `q` the
  identity near that side of `p`.
- For each `m`, let `e in D` with `e^m = q`. Then `e` commutes with `q`, so it
  preserves `Fix(q)`. If `e(p) > p`, then `e^n(p)` increases with `n`, so
  `q(p) = e^m(p) > p`, which is false. Likewise `e(p) < p` is impossible, so
  `e(p) = p`. Then `e` is linear on that side of `p` with slope `2^(α/m)`, so `m | α`.
  This holds for every `m`, so `α = 0`, a contradiction.
- A nonzero homomorphism `Q -> Q` is injective, so `ρ|_D` is injective. Then
  `ρ(D) ≅ Q` inside `Q` forces `ρ(D) = Q`. Nontrivial elements of `D` have `ρ ≠ 0`,
  hence no fixed points, so `D` acts freely. And `2^j = 2` gives `j = 1`.

**Step 2 (normalization).**
- `g in δ^K T-bar δ^-K` for some `K`. Conjugate `D` and `t` by `δ^-K`. The new
  `t` is `(δ^-K g δ^K) δ` with `δ^-K g δ^K in T-bar`.
- The relation `t q t^-1 = q^2` and the properties of Step 1 are preserved. So from
  now on `g` commutes with `τ_1`, and `C := sup |g - id| < ∞`.

**Step 3 (item 2).**
- Put `g_i = δ^-i g δ^i`, so `g_i(x) = 2^-i g(2^i x)`. Then `g_i` commutes with
  `τ_(2^-i)`, hence with `τ_1`, and `sup |g_i - id| = 2^-i C`.
- By induction, `h_m := δ^-m t^m = g_m g_(m-1) ... g_1`. Indeed
  `δ^-(m+1) t^(m+1) = (δ^-(m+1) g δ^(m+1)) (δ^-m t^m)`.
- `sup |h_(m+1) - h_m| <= 2^-(m+1) C`, so `h_m -> h` uniformly. `h` is a uniform
  limit of increasing homeomorphisms commuting with `τ_1`. So it is continuous,
  non-decreasing, commutes with `τ_1`, and has `sup |h - id| <= C`, hence is onto.
- `h_m ∘ t = δ^-m t^(m+1) = δ ∘ h_(m+1)`. Letting `m -> ∞` gives `h ∘ t = δ ∘ h`.
- For `q in D`: `h_m ∘ q = δ^-m (t^m q t^-m) t^m = A_m ∘ h_m`, where
  `A_m = δ^-m q^(2^m) δ^m`. Let `q` commute with `τ_L`. By (F1),
  `|A_m(x) - x - ρ(q)| = 2^-m |q^(2^m)(2^m x) - 2^m x - 2^m ρ(q)| < 2^-m L`. So
  `A_m -> τ_(ρ(q))` uniformly.
- Hence `|h(q(x)) - h(x) - ρ(q)| <= |h - h_m| (q x) + |A_m(h_m x) - h_m x - ρ(q)| + |h_m x - h x|`,
  and this tends to `0`. So `h ∘ q = τ_(ρ(q)) ∘ h`.

**Step 4 (item 3).**
- If `t = δ`, then `h_m = id`, so `h = id`. Item 2 then gives `q = τ_(ρ(q))` for
  every `q in D`, so `D = {τ_s : s in Q}` by Step 1.
- But `τ_(1/3)` does not preserve `Z[1/2]`, and every element of `T-check` does. So
  this is a contradiction.
- If `t = k δ k^-1` with `k in T-check`, apply this to `(k^-1 D k, δ)`.

**Step 5 (item 4).**
- For `x in Z[1/2]` and `q in D`, `q(x) in Z[1/2]` and `h(q(x)) = h(x) + ρ(q)`. So
  `h(x) + Q ⊆ S := h(Z[1/2])`.
- Suppose `h(y) = λy + e` on an open interval `J`, with `λ > 0`. Put `U = h(J)`,
  an open interval. Since `h` is non-decreasing and strictly increasing on `J`,
  `h^-1(v)` is a single point of `J` for each `v in U`.
- So `S ∩ U = λ(Z[1/2] ∩ J) + e`, and differences of points of `S ∩ U` lie in
  `λ Z[1/2]`. But `S ∩ U ⊇ (h(x_0) + Q) ∩ U` for a dyadic `x_0`. That set contains
  some `v` and `v + 3^-N` for all large `N`.
- So `λ^-1 3^-N in Z[1/2]` for all large `N`. The quotient of two consecutive such
  numbers is `3`. So `λ^-1 3^-N in 3^k Z[1/2]` for every `k`, forcing
  `λ^-1 3^-N = 0`, which is absurd.

**Step 6 (item 5).**
- **From `h` to `(u, η)`.** Let `h` be injective, hence a homeomorphism commuting
  with `τ_1`, inducing `η` on `R/Z`. Since `g in T-bar`,
  `t(x + 1/2) = g(2x + 1) = t(x) + 1` and `t(x + 1) = t(x) + 2`. So `t` is the lift of
  a PL-dyadic degree-2 circle map `u` with `u(θ + 1/2) = u(θ)`, and `h ∘ t = δ ∘ h`
  gives `η ∘ u = D ∘ η`.
- By item 2, `q = h^-1 τ_(ρ(q)) h`. It commutes with `τ_1` and lies in `T-bar`, so
  it induces `η^-1 R_(ρ(q)) η in T`. As `ρ(D) = Q`, this holds for all `s in Q/Z`.
- **From `(u, η)` back to `D_2`.** Lift `η` to `h` commuting with `τ_1`, and lift
  `u` to `t` with `t(x + 1/2) = t(x) + 1`. Then `h ∘ t = δ ∘ h + j` for an integer
  `j`, and `h' = h + j` satisfies `h' ∘ t = δ ∘ h'`.
- `g := t δ^-1` commutes with `τ_1` and is PL-dyadic, so `g in T-bar` and
  `t in T-check`. Each `h'^-1 τ_s h'` (`s in Q`) is a lift of `η^-1 R_s η in T`, so it
  lies in `T-bar`.
- These form a copy of `(Q,+)` with `t q t^-1 = q^2`, since
  `h' t h'^-1 = δ` and `δ τ_s δ^-1 = τ_(2s)`.
