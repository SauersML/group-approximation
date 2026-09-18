---
rg: 2
id: almost-automorphism-torsion-subgroups-are-rf-proof
kind: route
title: The depth cocycle vanishes at fixed points of torsion elements, a pushdown pumping argument bounds it on finitely generated torsion subgroups, and bounded depth change gives finite permutation quotients
target: almost-automorphism-torsion-subgroups-are-rf
requires:
  - restricted-burnside-finiteness
---

Notation as in the claim. Words are read from the root: in `x = x_1 x_2 …`, `x_1` is at depth 1.
`d(x,y) = d^(−|common prefix|)` is the standard ultrametric. Every `k ∈ Aut(X*)` is a length-preserving
bijection on words and an isometry of `X^ω`, and `k(a w) = k(a) k|_a(w)`.

## Step 0. The depth cocycle

For `h ∈ 𝒩_d` and `x ∈ X^ω`, choose a piece of (AA) containing `x`, say `x ∈ [u]` with `h(u w) = v g(w)`, and put
`c(h,x) = |v| − |u|`.

- **Well defined.** Refining a piece replaces `(u, v, g)` by `(u a, v g(a), g|_a)` for a word `a`, which keeps
  `|v| − |u|`. Two pieces at `x` have a common refinement `[p]` with `p` a prefix of `x`, giving
  `h(p w) = q k(w) = q' k'(w)` for all `w`, with `k, k' ∈ Aut(X*)`. If `|q'| = |q| + r` with `r > 0`, then `q' = q t`
  with `|t| = r` and `k(w) = t k'(w)` for all `w`. Then the bijection `k` of `X^ω` would have image inside `[t]`,
  which is impossible. So `|q| = |q'|`.
- **Cocycle.** Composing pieces gives `c(h h', x) = c(h, h' x) + c(h', x)`. `c(h, ·)` is locally constant, and
  `c(1, x) = 0`.

## Step 1. Torsion elements have zero depth change at their fixed points

If `h` has finite order `N` and `h x = x`, then `c(h, x) = 0`. Indeed, the cocycle identity at the fixed point gives
`c(h^m, x) = m c(h, x)`, and `c(h^N, x) = c(1, x) = 0`.

**Contraction corollary.** Suppose that for a word `T`, a nonempty word `y` and some `k ∈ Aut(X*)`, an element
`h ∈ 𝒩_d` satisfies `h(T w) = T y k(w)` for all `w`. Then `h` has infinite order. The map `T w ↦ T y k(w)` sends the
complete ultrametric space `[T]` into itself and multiplies distances by `d^(−|y|) < 1`. So it has a fixed point
`x* ∈ [T]`, which is fixed by `h`, with `c(h, x*) = |y| > 0`. Now apply Step 1.

## Step 2. Uniform bound on the depth cocycle (pumping)

Let `H = ⟨S⟩` be torsion with `S = S^(−1)` finite. Write each `s ∈ S` in the form (AA), and choose `D` at least the
length of every code word used, and `K = max |c(s, x)|` over `s ∈ S`, `x ∈ X^ω`. Put `B = K · d^(D+K)`.

**Claim.** `|c(h, x)| <= B` for all `h ∈ H` and `x ∈ X^ω`.

*Proof.* Write `h = s_m ⋯ s_1` and put `x_0 = x`, `x_i = s_i x_(i−1)`, `ht(i) = c(s_i ⋯ s_1, x) = Σ_(j<=i) c(s_j, x_(j−1))`.
Suppose `M := ht(m) > B`. The case `ht(m) < −B` follows by applying this to `h^(−1)` at `h x`, since
`c(h^(−1), h x) = −c(h, x)`.

*Record times.* For each integer level `0 <= ℓ < M`, let `t_ℓ = max{ i : ht(i) <= ℓ }`. Then `ht(t_ℓ) ∈ (ℓ − K, ℓ]`, and
`ht(i) > ℓ >= ht(t_ℓ)` for all `i > t_ℓ`. Distinct values of `ht(t_ℓ)` give distinct times, and there are at least
`M / K > d^(D+K)` of them. So there are record times `t < t'` whose points `x_t, x_(t')` have the same first
`D + K` letters `T`. Since `t` is a record time, `ht(t') > ht(t)`; put `r = ht(t') − ht(t) > 0`.

*The segment only touches the top.* Write `x_t = T z`. For `t <= i <= t'`, we show by induction that
`x_i = T_i k_i(z)` with `T_i` a word of length `D + K + ht(i) − ht(t) >= D + K`, `k_i ∈ Aut(X*)`, and that `T_(i+1)`
depends only on `T_i` and `s_(i+1)`, not on `z`.

- The base case is `T_t = T`, `k_t = 1`.
- For the step, `s = s_(i+1)` reads a code word `u_j` of length `<= D <= |T_i|`, so `u_j` is a prefix of `T_i`.
  Write `T_i = u_j T'`. Then
  `s(x_i) = v_j g_j(T' k_i(z)) = v_j g_j(T') · (g_j|_(T') k_i)(z)`.
- So `T_(i+1) = v_j g_j(T')`, of length `|T_i| + c(s, x_i) = D + K + ht(i+1) − ht(t)`. This is `>= D + K`, because
  `ht(i+1) >= ht(t)` for `i+1 > t`. Also `k_(i+1) = g_j|_(T') k_i`.

The same computation applies verbatim to every point `T z'`, `z' ∈ X^ω`. So `h' := s_(t') ⋯ s_(t+1) ∈ H` satisfies
`h'(T z') = T_(t') k(z')` for all `z'`, with `k = k_(t') ∈ Aut(X*)`. Now `|T_(t')| = D + K + r`, and its first
`D + K` letters are `T`. So `T_(t') = T y` with `|y| = r > 0`. By the contraction corollary `h'` has infinite order,
contradicting that `H` is torsion. ∎

## Step 3. Elements of H are single pieces on deep cones

Put `L = D + B`. **Claim:** every `h ∈ H` maps every cone `[p]` with `|p| >= L` onto a cone `[q]` as a single piece,
`h(p w) = q k(w)` with `k ∈ Aut(X*)`, and `|q| = |p| + c(h, ·) ∈ [|p| − B, |p| + B]`.

Induct on the length of `h = s_m ⋯ s_1`. If `h_0 = s_(m−1) ⋯ s_1` maps `[p]` onto `[q_0]` as a single piece, then
`|q_0| >= |p| − B >= D` by Step 2 (applied to `h_0 ∈ H`). So `s_m` acts on `[q_0]` through one code word
(`|q_0| >= D`), as `q_0 w ↦ q' k'(w)`. Composing gives a single piece for `h`.

## Step 4. Finite quotients

Fix `n >= D + 2B` and let `F_n = { h[p] : h ∈ H, |p| = n }`. This is a set of cones of depth in `[n − B, n + B]`, so
it is finite.
- **Action.** For `[q] = h_1[p] ∈ F_n` and `h ∈ H`, Step 3 applies to `[q]` (depth `>= n − B >= L`), and
  `h[q] = (h h_1)[p] ∈ F_n`. So `H` permutes the finite set `F_n`.
- **Kernels.** Let `K_n ⊴ H` be the kernel, of finite index. Every `h ∈ ⋂_n K_n` maps every cone of every depth
  `>= D + 2B` onto itself. Points are intersections of nested cones, so `h` fixes every point and `h = 1`. So `H` is
  residually finite (item 1).
- **Refinement (item 2).** If `h ∈ K_n`, then by Step 3 `h` acts on each depth-`n` cone `[p]` as
  `p w ↦ p k_p(w)`, with `k_p` the product of the generator states met along the way. If `H ≤ V_d(G)`, all these
  states lie in `G`, and `h ↦ (k_p)_(|p| = n)` embeds `K_n` in `G^(d^n)`. For `G = 1` every `k_p = 1`, so `K_n = 1`
  and `H` embeds in the finite group `Sym(F_n)`.

## Step 5. Finite exponent (item 3)

A finitely generated group of finite exponent is torsion. By item 1 it is residually finite, so it is finite by
Zelmanov (`restricted-burnside-finiteness`: every finite `m`-generated group of exponent dividing `N` is a quotient
of the finite group `R(m,N)`, so a residually finite `m`-generated group of exponent `N` is a quotient of
`R(m,N)`). ∎

## Calibration

- **V.** For `G = 1`, item 2 is Röver's theorem that `V` is torsion locally finite (BCR arXiv:1402.3860v2, Thm 1.3,
  read at source; primary source Röver 1999 not read). Our proof is independent of his.
- **Röver's group.** For `G` the first Grigorchuk group, `V_2(G)` contains the infinite torsion group `G` itself, with
  unbounded exponent. That agrees with item 2 (`H = G`, `K_n ≤ G^(2^n)`) and shows that "residually finite" cannot
  be improved to "finite" once `G ≠ 1`.
- **Brin–Thompson.** The argument breaks for `nV`, `n >= 2`, exactly at Step 2. The depth becomes a vector, and a
  segment that is a record in one coordinate can still pop deep letters in another. So no conclusion is drawn for
  `nV`.
