---
rg: 2
id: baker-lifted-torus-generators-force-diagonal-lamp-shears-proof
kind: route
title: "Elements of nV preserve each coordinate's tail; a baker lift of the torus reads alpha and beta at each end of Z from opposite coordinate tails; a shear entry would then be a function of x alone and of y alone, hence constant up to a bounded passive part, which contradicts affine spanning"
target: baker-lifted-torus-generators-force-diagonal-lamp-shears
requires: []
---

Notation as in the target. Points of `C^n` are `p = (p_1, ..., p_n)`, and `p_i[d]` is the digit of
coordinate `i` at depth `d ≥ 0`. Write `x = p_1`, `y = p_2`, and `w = (p_3, ..., p_n)`.

## Step 0: the linear part of a lift is unique

- Suppose `φ∘s = a∘φ = a'∘φ`, with linear parts `γ` and `γ'`.
- Then `(γ − γ')φ(p) = v' − v` for all `p`.
- Pair this with any `μ ∈ M`: `⟨φ(p), (γ−γ')^* μ⟩` is constant in `p`.
- Affine spanning gives `(γ − γ')^* μ = 0` for all `μ`, so `γ = γ'`.
- Lifts compose: `(s_1 s_2, a_1 a_2)` is a lift. So the linear parts of all lifts form a group.

## Step 1: tail preservation in nV

By Brin's definition, `s ∈ nV` comes with a finite partition of `C^n` into rectangles
`U = u_1C × ... × u_nC` and words `u'_i` such that
`s(u_1 q_1, ..., u_n q_n) = (u'_1 q_1, ..., u'_n q_n)`.

Hence, for `p ∈ U` and every coordinate `i`:
- **(T1)** `s(p)_i[d] = p_i[d − |u'_i| + |u_i|]` for all `d ≥ |u'_i|`;
- **(T2)** the first `L` digits of `s(p)_i` are determined by `U` and the first `|u_i| + L`
  digits of `p_i`.

Let `E(s)` be the largest length of any `u_i` or `u'_i` over all rectangles of `s`.

## Step 2: Lemma W (baker lifts are side-split)

Put `φ~ = φ∘c`. Then `φ~∘B^k = h'∘φ~`, and `(s, a)` is a lift for `φ` iff `(c^-1 s c, a)` is a
lift for `φ~`. Since `c^-1 s c ∈ nV`, it suffices to treat `φ~`; rename it `φ`.

- **Shift coordinates.** Use `Θ(x, y) = z ∈ {0,1}^Z` with `z_d = x[d]` and `z_(−d−1) = y[d]`
  for `d ≥ 0`. Then `B` is the shift `(Sz)_i = z_(i+1)` on `z` and the identity on `w`
  (Step 7 of `char-p-burger-lamp-realizations-refute-haagerup-proof`).
- **Iterates.** Write `h'(ξ) = h^j ξ + v`. By induction, `h'^l(ξ) = h^(jl) ξ + v_l` for every
  `l ∈ Z`, with constants `v_l`. By the table in the target's setting,
  `(h^(jl)ξ)_(α,m) = α_(m−jl)` and `(h^(jl)ξ)_(β,m) = β_(m+jl)`.
- **Finite windows.** For each of the finitely many pairs `(ε, r)` with `ε ∈ {α,β}` and
  `0 ≤ r < |j|`, the map `ξ_(ε,r)∘φ` is continuous into `F_p`, hence locally constant. So there are
  `L, L'` such that every one of these maps depends only on `z_([−L', L'))` and the first `L`
  digits of each `w`-coordinate.
- **All coordinates.** Apply `φ∘B^(kl) = h'^l∘φ` at the coordinate `(α, r)`:
  `α_(r−jl)(z, w) = α_r(S^(kl) z, w) − (v_l)_(α,r)`.
  - The right side depends only on `z_([kl−L', kl+L'))` and the first `L` digits of `w`.
  - Similarly, `β_(r+jl)(z, w)` depends only on the same window.
  - Every `m ∈ Z` is `r − jl` for exactly one `(r, l)`, and also `r + jl` for exactly one `(r, l)`.
- **Sides.** Suppose `jk > 0`.
  - For `α_m` with `m → +∞`, we have `l → −∞·sgn(j)`, so `kl → −∞`. The window lies in the
    negative positions, which are `y`-digits of depth `≥ |kl| − L'`.
  - For `α_m` with `m → −∞`, we get `kl → +∞`: `x`-digits of depth `≥ kl − L'`.
  - For `β_m` it is the reverse: `x` at `+∞` and `y` at `−∞`.
  - For `jk < 0`, `kl` changes sign, which swaps `x` and `y`.
  - In both cases `S(α,±) ≠ S(β,±)`. The depths `D(m) = |k||l| − L'` tend to `∞` as `|m| → ∞`,
    and the passive bound `L` is uniform. So `φ` is side-split. ∎

The script `check_side_split.py` recovers this side table for Proposition B's `φ` by bit flips.

## Step 3: Theorem S, the lower-left entry vanishes

Let `(s, a)` be a lift. Write `A = (γ^-1)^T = [[a_11, a_12], [a_21, a_22]]` with entries in `R`,
and `a_21 = Σ_i c_i t^i`. The `β`-row of `φ∘s = a∘φ` reads, for all `m` and `p`:

```
β_m(s p) = G_m(p) + H_m(p) + v_(β,m),   G_m = Σ_i c_i α_(m+i),   H_m = Σ_i d_i β_(m+i)
```

where `a_22 = Σ_i d_i t^i`. Put `P = S(β,+)` and `Q = S(α,+)`, so `P ≠ Q`. Let `F` be the finite
set of `i` with `c_i ≠ 0` or `d_i ≠ 0`. Fix `m_1` such that for all `m ≥ m_1` and `i ∈ F ∪ {0}`,
`D(m+i) ≥ D_* := E(s) + 1`.

- **(i) Globally, `G_m` reads only deep `Q`-digits and shallow `w`.** For `m ≥ m_1`, `G_m(p)`
  depends only on the digits `p_Q[d]` with `d ≥ D_*` and the first `L` digits of `w`. This is the
  side-split hypothesis applied to each `α_(m+i)`.
- **(ii) On each rectangle, `G_m` reads only `P` and `w`.** Let `U` be a rectangle of `s` and
  `p ∈ U`. Then `G_m(p) = β_m(s p) − H_m(p) − v_(β,m)`.
  - `H_m(p)` depends only on `p_P` and `w(p)`.
  - `β_m(s p)` depends only on `s(p)_P[d]` for `d ≥ D(m) ≥ |u'_P|` and on `s(p)_w` to depth `L`.
    By (T1) and (T2), that is only on `p_P` and `w(p)`.

  So `G_m` restricted to `U` is a function of `(p_P, w)`.
- **Constant in `(x, y)` on `U`.** `U` is a product `U_P × U_Q × U_w`. For fixed `w ∈ U_w`,
  `G_m(·, ·, w)` is a function of `p_P` alone by (ii) and of `p_Q` alone by (i), on a product set,
  so it is constant. Thus `G_m|U = g_U(w)`.
- **Globalize.** Claim: `G_m(p) = G_m(p')` whenever `p, p'` agree in the first `L` digits of `w`.
  - Let `p''` have the `P`- and `w`-coordinates of `p'`. Its `Q`-coordinate agrees with `p'_Q` at
    depths `< D_*` and with `p_Q` at depths `≥ D_*`.
  - Rectangles of `s` are determined by prefixes of length `≤ E(s) < D_*`. So `p''` lies in the
    rectangle `U` of `p'` and has the same `w` as `p'`. Hence `G_m(p'') = g_U(w(p')) = G_m(p')`.
  - `p''` has the deep `Q`-digits of `p` and the same first `L` digits of `w` as `p`. By (i),
    `G_m(p'') = G_m(p)`.

  So `G_m = Ψ_m(w_(≤L))` for every `m ≥ m_1`. When `n = 2`, `Ψ_m` is a constant.

## Step 4: Theorem S, contradiction unless `a_21 = 0`

- **Characters.** Let `μ_m = (t^m a_21, 0) ∈ M`. By the pairing, `⟨φ(p), μ_m⟩ = G_m(p)`.
- **Independence.** If `a_21 ≠ 0`, the `μ_m` for `m ≥ m_1` are `F_p`-linearly independent: they
  have pairwise distinct lowest `t`-degrees.
- **Finite target.** All `G_m` lie in the space `Fn_L` of functions of the first `L` digits of the
  `n − 2` passive coordinates. It has `F_p`-dimension `2^(L(n−2))`.
- **Kernel.** Take `N > dim Fn_L` indices. There are `λ ∈ F_p^N \ {0}` with `Σ λ_m G_m = 0`. Then
  `μ = Σ λ_m μ_m ≠ 0` and `⟨φ(·), μ⟩ ≡ 0` is constant. This contradicts affine spanning.
- **Hence `a_21 = 0`.**
- **The other entry.** Run Steps 3 and 4 at the end `−∞` with the `α`-row
  `α_m(s p) = Σ a_11-terms + Σ_i b_i β_(m+i) + v_(α,m)`, with `P = S(α,−)` and `Q = S(β,−)`. This
  gives `a_12 = 0`.
- **Conclusion.** `A` is diagonal, and so is `γ = (A^T)^-1`. ∎ (Theorem S)

## Step 5: Theorem D

- By Lemma W and Theorem S, every lift of `φ~ = φ∘c` has diagonal linear part.
- By Step 2, the lifts of `φ` have the same affine maps.
- Diagonal elements of `GL_2(R)` are `diag(u, u')` with `u, u' ∈ R^× = F_p^× t^Z`. These form an
  abelian group that contains no `e_12(r)`, `e_21(r)` (`r ≠ 0`) or `w`.
- So the group generated by the linear parts of any family of lifts is abelian. It cannot
  contain `EL_2(R)`, which contains `e_12(1)`.
- The same holds when the baker map acts on any two coordinates `i ≠ i'` of `C^n`: the coordinate
  permutation normalizes `nV`. ∎

## Scope and honesty

- The class killed is exactly the realizations that have a baker lift of some nonzero power of
  `h`, up to `nV`-conjugacy. That includes Proposition B's `φ` for every `(p, k, τ)`.
- The kill uses only (T1) and (T2). So it holds verbatim in any group of homeomorphisms that acts
  by rectangle-wise prefix replacement.
- It says nothing about lifts of `h` that are not conjugate to baker powers. In particular, no
  statement about the Haagerup property of `2V` is made.
