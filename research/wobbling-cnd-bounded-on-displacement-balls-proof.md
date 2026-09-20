---
rg: 2
id: wobbling-cnd-bounded-on-displacement-balls-proof
kind: route
title: "Flux reduces a displacement ball to flux zero; a flux-zero wobble is a product of two block permutations; block groups are three-fold products of infinite powers of alternating groups, which are strongly bounded"
target: wobbling-group-cnd-functions-are-bounded-on-displacement-balls
requires: []
---

Notation as in the target. Throughout, `ψ` is a cnd function on a group `G`.

## Import (verbatim)

Y. de Cornulier, *Strongly bounded groups and infinite powers of finite groups*, Comm. Algebra
34 (2006), no. 7, 2337–2345, arXiv:math/0411466. Abstract, verbatim:

> "We define a group as strongly bounded if every isometric action on a metric space has bounded
> orbits. This latter property is equivalent to the so-called uncountable strong cofinality,
> recently introduced by G. Bergman. Our main result is that G^I is strongly bounded when G is a
> finite, perfect group and I is any set."

`G^I` is the full Cartesian product, as an abstract group. `A_N` is finite and perfect for
`N ≥ 5`, so **`A_N^J` is strongly bounded for every set `J` and every `N ≥ 5`**.

## Step 0 (standard facts about cnd functions)

- (0a) `ψ − ψ(e)` is again cnd, because `Σ c_i = 0` kills constants. So assume `ψ(e) = 0`. Then
  Schoenberg's GNS construction gives an affine isometric action of `G` on a real Hilbert space
  with cocycle `b` and `ψ(g) = ‖b(g)‖²`.
- (0b) `√ψ(gh) ≤ √ψ(g) + √ψ(h)`, because `b(gh) = b(g) + g·b(h)` and the linear part is
  orthogonal. Hence if `ψ` is bounded on subsets `S_1, …, S_k`, it is bounded on `S_1 ⋯ S_k`.
  With `S_1, S_3` singletons, `ψ` is bounded on `x S y` whenever it is bounded on `S`.
- (0c) If `H ≤ G` is strongly bounded, then `ψ` is bounded on `H`. The restricted affine action of
  `H` is isometric, so the orbit `{b(h)} = H·0` is bounded.

## Step 1 (flux)

Fix a fibre and suppress it from the notation. Put `H_m = (−∞, m)`. For `A ⊂ Z` with
`A Δ H_0` finite and `π ∈ W(Z)`, the set `πA Δ A` is finite, and we put
`ind_A(π) = |πA \ A| − |A \ πA|`.

- **Counting formula.** For any finite `J ⊇ πA Δ A`,
  `ind_A(π) = |πA ∩ J| − |A ∩ J|`, because both sets agree off `πA Δ A`.
- **Independence of `A`.** Let `A' = A ∪ {a}` with `a ∉ A`. Take a finite `J` that contains
  `πA Δ A`, `πA' Δ A'`, `a` and `πa`. Then `πa ∉ πA`, so `|πA' ∩ J| = |πA ∩ J| + 1` and
  `|A' ∩ J| = |A ∩ J| + 1`. So `ind_{A'}(π) = ind_A(π)`. Any two sets commensurate with `H_0` are
  joined by finitely many such moves, so `ind_A(π) =: φ(π)` is independent of `A`.
- **The cut counts.** With `A = H_m`, `F_m = |πH_m \ H_m|` and `B_m = |H_m \ πH_m|`. So
  `φ(π) = F_m − B_m` for every `m`.
- **Homomorphism.** With `J` large enough, `ind_A(πρ) = (|πρA ∩ J| − |ρA ∩ J|) + (|ρA ∩ J| − |A ∩ J|)
  = ind_{ρA}(π) + ind_A(ρ) = φ(π) + φ(ρ)`.
- `σH_m = H_{m+1}`, so `φ(σ) = 1`.
- **Bound.** If `disp(π) ≤ r`, every `n < m` with `π(n) ≥ m` lies in `[m−r, m)`, so
  `0 ≤ F_m ≤ r`. Likewise `0 ≤ B_m ≤ r`, so `|φ(π)| ≤ r`.

Now let `π ∈ W_r^0` have constant flux vector `(c, c, …)`, so `|c| ≤ r`. Then `π' = σ^{-c}π` has
flux zero on every fibre, and `disp(π') ≤ 2r`.

## Step 2 (a flux-zero wobble is a product of two block permutations)

Let `π'` have flux zero on every fibre and `disp(π') ≤ r'`, and let `L` be even with `L > 2r'`.

- `P` is the group of permutations of `Y` that preserve every block `[kL, (k+1)L) × {i}`. As an
  abstract group, `P ≅ S_L^{Z × I}`. Every such permutation has displacement `< L`, so `P ≤ W(Y)`.
- `P_{1/2}` is the same with blocks `[kL − L/2, kL + L/2) × {i}`. Then `P_{1/2} = σ^{L/2} P σ^{−L/2}`.

Fix a fibre and a cut `m = kL`.

- The forward crossings `Fw_m = {n < m : π'(n) ≥ m}` lie in `[m−r', m)`. Their images `Φ_m = π'(Fw_m)`
  lie in `[m, m+r')`.
- The backward crossings `Bw_m = {n ≥ m : π'(n) < m}` lie in `[m, m+r')`. Their images
  `Ψ_m = π'(Bw_m)` lie in `[m−r', m)`.
- Flux zero gives `|Φ_m| = |Ψ_m|`. Choose a bijection `β_m: Φ_m → Ψ_m`.

Define `p` on every fibre to be `β_m` on each `Φ_m`, `β_m^{-1}` on each `Ψ_m`, and the identity
elsewhere.

- **`p ∈ P_{1/2}`.** The windows `[m−r', m+r')` of different cuts are disjoint, because
  `2r' < L`. So `p` is a well-defined involution. Each window lies in the block
  `[m−L/2, m+L/2)`, because `r' < L/2`.
- **`pπ' ∈ P`.** Take `n ∈ [kL, (k+1)L)`. Since `|π'(n) − n| ≤ r' < L/2`, the point `n` crosses at
  most one cut. Because `π'` is injective, `π'(n) ∈ Φ_m` exactly when `n ∈ Fw_m`, and
  `π'(n) ∈ Ψ_m` exactly when `n ∈ Bw_m`.
  - If `n` crosses no cut, then `π'(n)` is in the block of `n` and in no `Φ` or `Ψ`. So
    `pπ'(n) = π'(n)` stays in the block.
  - If `n ∈ Fw_m`, then `m = (k+1)L`, and `pπ'(n) ∈ Ψ_m ⊂ [m−r', m)`, which is inside the block.
  - If `n ∈ Bw_m`, then `m = kL`, and `pπ'(n) ∈ Φ_m ⊂ [m, m+r')`, which is inside the block.

  So `pπ'` maps each finite block injectively, and hence bijectively, to itself.

Hence `π' = p · (pπ') ∈ P_{1/2} P`. With Step 1 (`r' = 2r`, `L > 4r`), every `π ∈ W_r^0` lies in
`σ^c · σ^{L/2} P σ^{−L/2} · P` for some `|c| ≤ r`. This is the first half of item 2 of the target.

## Step 3 (the parity fix: `P ⊆ A · Q' · Q`)

Assume also `L ≥ 5`. Index the blocks of all fibres together by `(k, i)`. Let `t_{k,i}` be the
transposition of the first two points of block `(k, i)`.

- `A = Π_{k,i} Alt(block_{k,i}) ≅ A_L^{Z×I}`.
- `Q` is the product, over all `j` and `i`, of `Alt(block_{2j,i} ∪ block_{2j+1,i})`. So
  `Q ≅ A_{2L}^{Z×I}`.
- `Q'` is the same product with the pairs `block_{2j+1,i} ∪ block_{2j+2,i}`.

For `E ⊆ Z × I`, let `τ_E = Π_{(k,i) ∈ E} t_{k,i}`. This is a product of disjoint commuting
transpositions, so it lies in `P`, and `τ_E τ_{E'} = τ_{E Δ E'}`.

Every `s ∈ P` can be written `s = a · τ_E`, with `a ∈ A` and `E` the set of blocks on which `s` is
odd. Fix `E`, with indicator `ε`. Define `f: Z × I → {0,1}` on each fibre `i` by `f(0,i) = 0` and
the two rules

  `f(2j+1, i) = f(2j, i) + ε(2j, i) + ε(2j+1, i) (mod 2)`,  `f(2j+2, i) = f(2j+1, i)`,

used forwards for `j ≥ 0` and solved backwards for `j < 0`. Let `F = {f = 1}`.

- `τ_F` is even on each pair `{2j+1, 2j+2}`, since `f(2j+1) = f(2j+2)`. So `τ_F ∈ Q'`.
- `τ_{E Δ F}` has parity `ε + f` on block `k`. The first rule says
  `(ε + f)(2j) = (ε + f)(2j+1)`, so `τ_{E Δ F}` is even on each pair `{2j, 2j+1}`. So
  `τ_{E Δ F} ∈ Q`.

Therefore `s = a · τ_F · τ_{E Δ F} ∈ A · Q' · Q`.

## Step 4 (assembly)

Take `L` even with `L > 4r` and `L ≥ 6`.

- `A`, `Q` and `Q'` are isomorphic to `A_L^{Z×I}` or `A_{2L}^{Z×I}`, with `L, 2L ≥ 5`. By the
  import they are strongly bounded, and by (0c) `ψ` is bounded on each of them.
- By (0b) and Step 3, `ψ` is bounded on `P`, hence on `σ^{L/2} P σ^{−L/2}`, hence on
  `σ^c σ^{L/2} P σ^{−L/2} P` for each of the finitely many `|c| ≤ r`.
- By Step 2 this set covers `W_r^0`. This proves items 1 and 2 of the target.

## Step 5 (the full shift, item 3)

- **Setup.** Let `Y ⊂ X` be nonempty, `σ`-invariant, and made of aperiodic points. Choose a base
  point `y_i` in each orbit. Since `σ^n y ↦ n` is a bijection on each orbit, this gives
  `Y ≅ Z × I`.
- **`ι` is a homomorphism into `W(Y)`.** For `g ∈ [[X]]`, `ι(g) = g|_Y` preserves each orbit, is a
  bijection because `g` is a homeomorphism preserving orbits, and moves `σ^n y_i` to
  `σ^{n + k_g(σ^n y_i)} y_i`. So `disp(ι(g)) ≤ ‖k_g‖_∞`, and `ι` is a homomorphism.
- **The flux of `ι(g)` is constant.** For `x ∈ X` put
  `Φ_g(x) = #{n < 0 : n + k_g(σ^n x) ≥ 0} − #{n ≥ 0 : n + k_g(σ^n x) < 0}`. Only `|n| ≤ ‖k_g‖_∞`
  contribute, so `Φ_g` is a finite sum of indicators of clopen sets and is continuous.
  - Substituting `n ↦ n + m` shows that the flux of `ι(g)` at cut `m` on the orbit of `x` is
    `Φ_g(σ^m x)`.
  - By Step 1 this does not depend on `m`, so `Φ_g(σ^m x) = Φ_g(x)` for aperiodic `x`.
  - Aperiodic points with dense orbit exist in the full shift. So the continuous function `Φ_g` is
    constant on a dense orbit, hence constant on `X`.
  - So `φ(ι(g))` is the constant vector `Φ_g`, and `ι(B_r) ⊆ W_r^0`.
- **Conclusion.** By item 1, `ψ ∘ ι` is bounded on `B_1`.
- **`B_1` is infinite.** Take the involutions `g_m` of the w16 attempt on
  `full-shift-topological-full-group-is-a-t-menable`. Take an aperiodic `x*` with `x*_0 ≠ x*_1` and
  `E_m = [x*_{[−m,m]}]`, so that `E_m ∩ σE_m = ∅`. Let `g_m = σ` on `E_m`, `σ^{-1}` on `σE_m`, and
  the identity elsewhere. Then `k_{g_m}` takes the values `1`, `−1` and `0`. The supports
  `E_m ∪ σE_m` are pairwise distinct, so the `g_m` are pairwise distinct.
- A proper function has finite sublevel sets, so `ψ ∘ ι` is not proper. ∎
