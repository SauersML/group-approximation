---
rg: 2
id: z2-sft-boundary-hosts-need-unboundedly-hard-sft-languages-proof
kind: route
title: Evaluate the host on the orbit representation at δ_e, read the answer off one Ω-window and one boundary prefix, and apply the complexity-bounded non-universality principle
target: z2-sft-boundary-hosts-need-unboundedly-hard-sft-languages
requires:
  - complexity-bounded-host-classes-are-not-universal
---

Notation:
- `Ω ⊆ Σ^(Z^2)` is a `Z^2`-SFT with the product topology, and `(z·ω)(y) = ω(y − z)`.
- `∂F_d` is the space of infinite reduced words in a free basis `a_1, …, a_d`, with the cylinder
  topology, and `h·ξ` is the reduced form of the concatenation `hξ`.
- `B_Ω = LC(Ω, F_2) ⋊ Z^2` and `L = L_∂(d) = LC(∂F_d, F_2) ⋊ F_d` are the algebraic crossed products.
  - They have invertible `v_z`, `w_h` with `v_z g v_z^(-1) = g∘z^(-1)` and
    `w_h k w_h^(-1) = k∘h^(-1)`.
  - As vector spaces, `B_Ω = ⊕_z LC(Ω) v_z` and `L = ⊕_h LC(∂F_d) w_h`. Each is universal for
    covariant pairs.
- `P = Z^2 × F_d` has word length `|(z,h)| = |z|_1 + |h|`.
- `Q_R = [−R, R]^2`.

## Step 1. A faithful family of orbit representations

For `x = (ω, ξ) ∈ Ω × ∂F_d`, let `V = F_2^(P)` be the space of finitely supported functions on
`P`, with basis `δ_q`.
- `π_ω` of `B_Ω` on `F_2^(Z^2)` is defined by `π_ω(g) δ_z = g(z·ω) δ_z` and
  `π_ω(v_y) δ_z = δ_(y+z)`.
- `π_ξ` of `L` on `F_2^(F_d)` is defined the same way.

**Covariance.**

```text
π_ω(v_y) π_ω(g) π_ω(v_y)^(-1) δ_z = g((z − y)·ω) δ_z = (g∘y^(-1))(z·ω) δ_z .
```

So `π_ω` is a representation by universality, and likewise `π_ξ`. Put
`π_x = π_ω ⊗ π_ξ` on `F_2^(Z^2) ⊗ F_2^(F_d) = V`.

**Lemma 1.** If `b ∈ B_Ω ⊗ L` and `π_x(b) δ_e = 0` for every `x`, then `b = 0`.

*Proof.*
- Distributing the direct sums, `b = Σ_((z,h)) F_(z,h) (v_z ⊗ w_h)` with finitely many nonzero
  `F_(z,h) ∈ LC(Ω) ⊗ LC(∂F_d)`.
- `π_x(b) δ_e = Σ F_(z,h)(z·ω, h·ξ) δ_((z,h))`. Here `F(ω', ξ')` denotes the image of `F` under
  the multiplication map `m : LC(Ω) ⊗ LC(∂F_d) -> Fun(Ω × ∂F_d)`.
- Since `(ω, ξ) ↦ (z·ω, h·ξ)` is a bijection, every `m(F_(z,h))` vanishes.
- `m` is injective. Write `F = Σ_i g_i ⊗ k_i` with the `g_i` linearly independent. If `m(F) = 0`,
  then for each `ξ` we have `Σ_i k_i(ξ) g_i = 0`, so every `k_i(ξ) = 0`.
- Hence `b = 0`. `∎`

## Step 2. Locality

Fix a finite generating set `S = S^(-1)` of `G` and an injective homomorphism
`φ : F_2[G] -> B_Ω ⊗ L`.

**Finite data.**
- Write each `φ(s)`, `s ∈ S ∪ {1}`, as `Σ_(p ∈ S_s) F_(s,p) v_p` with `S_s ⊆ P` finite and
  `v_(z,h) = v_z ⊗ w_h`.
- Each `F_(s,p)` is a finite sum of products of locally constant functions. By compactness it is
  constant on every cylinder `{ω : ω|_(Q_r) = β} × {ξ : ξ|_r = u}` for some `r`.
- Let `m = max |p|` over all `p ∈ ∪ S_s`.

**Iteration.** For a word `w = s_1 ⋯ s_l`, the vector `π_x(φ(s_1)) ⋯ π_x(φ(s_l)) δ_e` is obtained
from `δ_e` by `l` applications of

```text
π_x(φ(s)) δ_q = Σ_(p ∈ S_s) F_(s,p)(pq·x) δ_(pq) .
```

After `k` applications the support lies in the ball `B_P(km)`.
- The only values used are `F_(s,p)(q·x)` with `|q| <= lm`.
- For `q = (z,h)`, `(z·ω)|_(Q_r)` is determined by `ω|_(Q_(r+|z|))`.
- The first `r` letters of `h·ξ` are determined by `h` and the first `r + |h|` letters of `ξ`,
  since at most `|h|` letters cancel.

So, with `R = r + lm`, both `π_x(φ(g_w)) δ_e` and `π_x(φ(1)) δ_e` are computable from the pair
`(ω|_(Q_R), ξ|_R)` and the finite data.

## Step 3. The word-problem algorithm

Since `φ` is injective and distinct group elements are linearly independent in `F_2[G]`:
- `g_w = 1` iff `φ(g_w) = φ(1)`;
- by Lemma 1, this holds iff `π_x(φ(g_w)) δ_e = π_x(φ(1)) δ_e` for all `x`.

The pairs `(ω|_(Q_R), ξ|_R)` with `x` in the space are exactly:
- the globally admissible `(2R+1) × (2R+1)` patterns `β` of `Ω`, each of which extends to some
  `ω ∈ Ω`;
- paired with the reduced words `u` of length `R`, each of which extends to an infinite reduced
  word.

**Algorithm.**
1. For each `β ∈ Σ^(Q_R)`, decide whether `β` is globally admissible.
2. For each admissible `β` and each reduced `u` of length `R`, compute the two vectors of Step 2
   and compare them.
3. Accept iff all comparisons agree.

**Cost.** Suppose the language is decided in time `t(n)`, and put `t̂(n) = max_(k <= n) t(k)`.
- There are at most `|Σ|^((2R+1)^2)` patterns and `(2d)^R` words.
- Each vector has support at most `|B_P(lm)| <= (2lm+1)^2 (2d)^(lm)`.
- Each coefficient lookup costs `poly(R)` on a multitape machine.

So the total is at most `2^(C_1 R^2) (t̂(2R+1) + 1)`. With `R <= (r+m) l` for `l >= 1`, this is at
most `2^(C l^2) (t̂(C l) + 1)`, for a constant `C >= 1` depending on `G, S, φ, Ω, d`. This proves the
displayed word-problem bound of the target.

## Step 4. Non-universality

Let `T` be recursive and put `T'(n) = 2^(n^2) (max_(k <= n) T(k) + n^2 + 1)`, which is recursive.

Suppose `Ω` is `T`-decidable with constant `C_Ω`. Then `t̂(n) <= C_Ω(max_(k<=C_Ω n) T(k) + n^2 + 1)`.
By Step 3, every `G` with `F_2[G]` embedded in some `B_Ω ⊗ L_∂(d)` has a word-problem algorithm
within `C_G · T'(C_G l)` for a constant `C_G >= 1`:
- `2^(C l^2) <= 2^((C' l)^2)`;
- the factor `C_Ω(max_(k<=C_Ω C l) T(k) + (Cl)^2 + 1)` is at most `C''(max_(k <= C'l) T(k) + (C'l)^2 + 1)`,
  with `C' = C·C_Ω` and `C'' = C_Ω`.

Let `K` be the class of all such `G`, over all `T`-decidable `Ω` and all `d >= 1`. Every member has,
for some finite generating set, a word-problem algorithm in time `C_G T'(C_G l) + C_G l + C_G`.

By `complexity-bounded-host-classes-are-not-universal` (ESTABLISHED), applied to `K` and `T'`,
there is a two-generated `H` with solvable word problem that embeds in no member of `K`. If
`F_2[H]` embedded injectively in some `B_Ω ⊗ L_∂(d)` with `Ω` `T`-decidable, then `H ∈ K`, and `H`
embeds in itself, a contradiction. `∎`

## Remarks

- The argument uses only that the Cantor factor over `F_d` has all reduced words as prefixes.
  - It applies verbatim to `B_Ω` alone (`d` absent), and to any field in which arithmetic is
    effective.
  - For an infinite field, the finite data are finitely many field elements.
- Over `Z^2` alone, the bound is `2^(O(l^2)) t̂(O(l))`. The `F_d` factor adds only a single
  exponential in `l`, which is absorbed.
