---
rg: 2
id: twisted-brin-thompson-logarithmic-depth-proof
kind: route
title: Brick maps of SV_G shift cylinder depth by at most their longest prefix, twists shift it by zero, so depth rates are invariant, homogeneous and logarithmic on power conjugates, while stripping a codeword per step gives linear growth
target: twisted-brin-thompson-power-conjugates-have-logarithmic-depth
requires:
  - depth-distortion-obstructs-power-conjugates-in-leavitt-hosts
  - twisted-brin-thompson-global-twists-are-conjugacy-closed
---

Notation is as in the target claim. A **brick** is a set `∏_s C(u_s) ⊆ C^S` in which only finitely many words `u_s`
are nonempty. For a word `β` and a coordinate `r`, `[β]_r = {x : x_r ∈ C(β)}`.

## Step 0: depth facts

- (D1) `depth(φψ) <= max(depth φ, depth ψ)`, and the same holds for sums.
- (D2) `depth(1_{[β]_r}) = |β|` for nonempty `β`.
  - The upper bound `<=` is clear.
  - For `>=`, take `x ∈ [β]_r` and let `x'` be `x` with bit `|β|` of coordinate `r` flipped. Then `x` and `x'`
    agree in the first `|β| - 1` bits of every coordinate, but the indicator separates them.
- (D3) For `f ∈ SV_G` put `f_* φ = φ ∘ f^-1`. Then `(fh)_* = f_* h_*`, and `f_*` fixes the constant functions,
  which have depth `0`.

## Step 1: finiteness, subadditivity, twists

- **Nonnegativity.** By (D3), a constant `φ` gives `depth(f_*φ) - depth φ = 0`, so `s(f) >= 0`.
- **Subadditivity.** For `f, h ∈ SV_G` and every `φ`,
  `depth((fh)_*φ) = depth(f_*(h_*φ)) <= depth(h_*φ) + s(f) <= depth φ + s(h) + s(f)`.
- **Twists.** `(τ_g^-1 y)_s = y_{g s}`, so bit `ℓ` of each coordinate of `τ_g^-1 y` is bit `ℓ` of some coordinate
  of `y`. Hence `depth(φ ∘ τ_g^-1) <= depth φ`, so `s(τ_g) <= 0`, and with nonnegativity `s(τ_g) = 0`.
- **One-coordinate Thompson elements.** Let `v ∈ V` act in coordinate `r`, with table `C(p_j) -> C(q_j)`,
  `p_j w ↦ q_j w`, and let `L` be the longest word in the table.
  - For `y` with `y_r ∈ C(q_j)`, the index `j` is determined by the first `L` bits of `y_r`.
  - Bit `ℓ` of `(v^-1 y)_r` is bit `ℓ` of `p_j` if `ℓ <= |p_j|`. Otherwise it is bit `ℓ - |p_j| + |q_j| <= ℓ + L`
    of `y_r`. The other coordinates are unchanged.
  - So if `depth φ = k`, then `φ ∘ v^-1` is determined by the first `k + L` bits of every coordinate. Hence
    `s(v) <= L`.
- **`V ≀ G`.** Every element is a finite product of one-coordinate Thompson elements and one twist. By
  subadditivity, `s < ∞` on `V ≀ G`.

**General `f ∈ SV_G`.**
- Every point has a neighbourhood on which `f` agrees with an element of `V ≀ G`. Shrink each neighbourhood to a
  brick. By compactness finitely many bricks suffice.
- A finite intersection of bricks is a brick or empty. The difference of two bricks is a finite union of bricks.
  So the cover refines to a partition `B_1, …, B_m` of `C^S` into bricks, with `f|B_i = w_i|B_i` and
  `w_i ∈ V ≀ G`.
- The sets `f(B_i)` are clopen and partition `C^S`. Let `D = max_i depth(1_{f(B_i)})`, which is finite.
- For `y ∈ f(B_i)` we have `f^-1 y = w_i^-1 y`. So `f_*φ = Σ_i 1_{f(B_i)} · (w_i)_*φ`.
- By (D1), `depth(f_*φ) <= max(D, depth φ + max_i s(w_i)) <= depth φ + max(D, max_i s(w_i))`.

So `s(f) < ∞`. This proves item 1. Nothing here needs `S` to be finite, since each function and each brick involves
only finitely many coordinates.

## Step 2: invariance and homogeneity (item 2)

- **Limit.** `n ↦ s(f^n)` is subadditive and nonnegative. By Fekete, `lim s(f^n)/n` exists, and the same holds for
  `f^-1`. So `ε(f) = lim E_f(n)/n` exists and is finite.
- **Conjugation.** `s(h f^n h^-1) <= s(h) + s(f^n) + s(h^-1)`, and the same holds for `f^-n`. So
  `E_{hfh^-1}(n) <= E_f(n) + s(h) + s(h^-1)`, and symmetrically. Dividing by `n` gives `ε(hfh^-1) = ε(f)`.
- **Homogeneity.** `E_{f^k}(n) = E_f(|k| n)`, so `ε(f^k) = |k| ε(f)`.

This is Step 1 of `depth-distortion-power-conjugates-leavitt-hosts-proof`. The only change is that nonnegativity
now comes from constants rather than from a dimension count, which fails for infinite `S`.

## Step 3: the logarithmic law (item 3)

**Reducing to `k >= 2`.** Suppose `h f h^-1 = f^k` with `|k| >= 2`. If `k < 0`, then `h^2 f h^-2 = f^(k^2)`, so we
may replace `(h, k)` by `(h^2, k^2)`. So assume `k >= 2`. Then `h^j f^d h^-j = f^(d k^j)` for all `j >= 0` and all
`d ∈ Z`.

**The word.** Let `n >= 1` have base-`k` digits `d_0, …, d_{M-1}`, so `0 <= d_j < k` and `M <= log_k n + 1`. The
factors `h^j f^(d_j) h^-j = f^(d_j k^j)` commute, and their product telescopes to
`f^n = f^(d_0) h f^(d_1) h f^(d_2) h ⋯ h f^(d_{M-1}) h^-(M-1)`.

**The bound.** By subadditivity,
`s(f^n) <= (M-1)(s(h) + s(h^-1)) + M (k-1) s(f)`.
The same word with `f^-1` in place of `f` (note `h f^-1 h^-1 = f^-k`) bounds `s(f^-n)` with `s(f^-1)`. Since
`M <= 2 log_2 n` for `n >= 2`, this gives
`E_f(n) <= 2 (s(h) + s(h^-1) + (k-1) max(s(f), s(f^-1))) log_2 n`. ∎

## Step 4: the Baumslag--Gersten tower (item 4)

Let `A`, `T` be the images of `a`, `t`, and put `B = T A T^-1`, so that `B A B^-1 = A^2`. Step 3 of
`depth-distortion-power-conjugates-leavitt-hosts-proof` uses only subadditivity and the conjugation estimate, which
hold here by Step 1. Explicitly:
- `A^(±2^m) = B^m A^(±1) B^-m`;
- `s(B^(±m)) <= s(A^(±m)) + s(T) + s(T^-1)`.

So `E_A(2^m) <= 2 E_A(m) + c` with `c = E_A(1) + 2(s(T) + s(T^-1))`. Iterating along `N_{i+1} = 2^{N_i}` gives
`E_A(N_i) + c <= 2^i (E_A(1) + c)`. ∎

## Step 5: linear witnesses (item 5)

**(a) Thompson elements.** Let `v ∈ V` have infinite order. By Step 5 of
`depth-distortion-power-conjugates-leavitt-hosts-proof`, citing Brin (Publ. IHES 84, 1996) and Salazar-Díaz
(IJAC 20, 2010) through revealing pairs, there are a word `α`, a nonempty word `γ` and `p >= 1` with
`v^p(αw) = αγw` for all `w`. So `v^p(C(α)) = C(αγ)`.

Place `v` in coordinate `r`, and put `φ = 1_{[α]_r}`. Then
`(v^(pj))_* φ = 1_{v^(pj)([α]_r)} = 1_{[αγ^j]_r}`,
which has depth `|α| + j|γ|` by (D2). So `s(v^(pj)) >= j|γ|`, and `ε(v) >= |γ|/p`.

**(b) Renormalization conjugators.** Take the setting of `renormalizable-thompson-elements-give-baumslag-solitar`:
- `X` carries `kV`, and `X = ⊔_{i<m} T^i A` with `m >= 2`;
- `c_0, …, c_{m-1}` is a complete prefix code, so every `c_i` is nonempty;
- `g(T^i a, y) = (φ(a), c_i y)`, placed on `k + 1` coordinates of `S`, with the last one called `r`. Here
  `(k+1)V` embeds in `SV_G` by acting on those coordinates and fixing the rest, by item 2 of
  `fg-subgroups-of-gl-n-q-in-twisted-bt-proof`. This needs `|S| >= k + 1`.

Now iterate `g^-1`:
- For `z ∈ C(c_i)`, write `z = c_i y`. Then `g^-1(x', z) = (T^i φ^-1(x'), y)`. So coordinate `r` of `g^-1(x', z)`
  is `z` with its leading codeword removed, and which codeword that is depends only on `z`.
- Hence coordinate `r` of `g^-n(x)` is `σ^(P_n(z)) z`, where `z = x_r` and `P_n(z)` is the total length of the
  first `n` codewords in the unique factorization of `z`. In particular `P_n(z) >= n`.

The witness:
- Let `ψ` be the first bit of coordinate `r`, which has depth `1`.
- Then `(g^n)_* ψ (x) = ψ(g^-n x)` is bit `P_n(x_r) + 1` of `x_r`.
- Fix any `x` and put `P = P_n(x_r)`. Let `x'` be `x` with bit `P + 1` of coordinate `r` flipped.
  - The first `P` bits are unchanged, so `P_n(x'_r) = P`, and `(g^n)_*ψ` separates `x` from `x'`.
  - `x` and `x'` agree in the first `P >= n` bits of every coordinate.
- So `depth((g^n)_*ψ) >= n + 1`, which gives `s(g^n) >= n` and `ε(g) >= 1`. The same holds for `u = g^-1`, since
  `ε` is symmetric in `f` and `f^-1`.

In particular this covers the baker map `(x_0 w, y) ↦ (w, x_0 y)`, the case `k = 1`, `m = 2`.

**(c) Commuting repairs.** Suppose `f x = x f` and `ε(x) = 0`. Then `f^(±n) = (fx)^(±n) x^(∓n)`, so
`E_f(n) <= E_{fx}(n) + E_x(n)`. Dividing by `n`, `ε(f) <= ε(fx)`. Take `x = τ_π`:
- `ε(τ_π) = 0` by Step 1;
- `τ_π` commutes with an element supported on coordinates that `π` fixes pointwise;
- so the infinite-entropy repair `f τ_π` keeps `ε(f τ_π) >= ε(f)`. ∎

## Step 6: consequences (item 6)

- **Chains.** `a^-1 b a = b^2` is `h b h^-1 = b^2` with `h = a^-1`, and `b^-1 c b = c^2` is `h c h^-1 = c^2` with
  `h = b^-1`. Step 3 gives `E_b, E_c = O(log n)`. An element of Step 5 has `E >= c n` by invariance (Step 2): if
  `b = w f w^-1` with `f` from Step 5, then `ε(b) = ε(f) > 0`, which contradicts `ε(b) = 0`.
- **Higman.** `H4 = ⟨g_1, …, g_4 | g_{i+1} g_i g_{i+1}^-1 = g_i^2⟩` (indices mod 4). Every generator is conjugate to
  its own square.
- **Baumslag--Gersten.** `b a b^-1 = a^2`, and `b = t a t^-1` is conjugate to `a`, so `ε(b) = ε(a) = 0`. Item 4 is
  Step 4.
- **Scope.** A twist has `E ≡ 0` by Step 1, so a placement by twists satisfies everything here trivially.

## Step 7: failure of local periodicity (item 7)

- `g ↦ τ_g` is injective because the action is faithful.
- So for `g` of infinite order, `τ_g` has infinite order, while `s(τ_g^n) = 0` for all `n`.
- Over any field `K`, consider `K`-valued locally constant functions. `τ_g` preserves the depth filtration `V_k`
  (functions of depth `<= k`). But if `S` is infinite, `V_k` is infinite-dimensional, and `τ_g` acts on it by an
  infinite permutation of coordinates.
- So Step 4 of the Leavitt route (bounded depth over a finite field implies local periodicity) has no analogue
  here. The finite-dimensional input `dim V_k < ∞` is exactly what fails. ∎
