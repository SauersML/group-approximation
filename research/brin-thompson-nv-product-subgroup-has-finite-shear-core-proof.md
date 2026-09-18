---
rg: 2
id: brin-thompson-nv-product-subgroup-has-finite-shear-core-proof
kind: route
title: "Permutations reduce T_n to V^n; a shear conjugate of a product is a product only if one factor commutes with (or inverts) the shear, and V has trivial centre"
target: brin-thompson-nv-product-subgroup-has-finite-shear-core
requires:
  - brin-thompson-triangular-subgroup-is-undistorted
  - thompson-v-finitely-presented-infinite-simple
---

Notation is as in the target.

**Step 0 (the maps are in nV).**
- *Permutations.* Conjugating a brick map `Π C(u_k) → Π C(v_k)` by `σ̂` permutes the words, so it
  is again a brick map. Hence `α_σ` is an automorphism of `nV`.
- *Shears.* `t^{(i,j)}_s` is, on each brick with `i`-th factor `C(1)` and `j`-th factor a table
  cylinder `C(u)` of `s`, the prefix replacement `u ↦ v` in coordinate `j`; on bricks with `i`-th
  factor `C(0)` it is the identity. So it is in `nV`, and `(t^{(i,j)}_s)^{-1} = t^{(i,j)}_{s^{-1}}`.

**Step 1 (item 1).**
- `V^n ⊆ α_σ(T_n)` for every `σ`: a product map `(a_1, ..., a_n)` satisfies
  `pr_k ∘ g = (a_1 × ... × a_k) ∘ pr_k` for every `k`, and `α_σ` permutes the factors.
- Conversely, let `g ∈ ⋂_σ α_σ(T_n)` and fix `i`. Take `σ` the transposition `(1 i)` (the identity
  if `i = 1`). Then `g' = α_σ^{-1}(g) ∈ T_n`, so by item 1 of
  `brin-thompson-triangular-subgroup-is-undistorted` (with `k = 1`, available since `n ≥ 2`) there is
  `h ∈ 1V = V` with `g'(y)_1 = h(y_1)` for all `y`. Since `σ̂` exchanges coordinates `1` and `i`,
  `g(x)_i = h(x_i)` for all `x`. Put `a_i = h`.
- Doing this for every `i` gives `g(x) = (a_1(x_1), ..., a_n(x_n))`, so `g = (a_1, ..., a_n) ∈ V^n`.

**Step 2 (key computation).** Let `h = (a_1, ..., a_n) ∈ V^n`, `t = t^{(i,j)}_s` with `s ≠ 1`.
Then `t^{-1}` applies `s^{-ε(x_i)}` to coordinate `j`, and, coordinate by coordinate,

```text
(t h t^{-1} x)_k = a_k(x_k)                               (k ≠ j)
(t h t^{-1} x)_j = β_{x_i}(x_j),   β_{x_i} = s^{ε(a_i x_i)} a_j s^{-ε(x_i)} ∈ V.
```

(Coordinate `i` of `h t^{-1} x` is `a_i x_i`, which decides whether `t` applies `s`.)
If `t h t^{-1} = (b_1, ..., b_n) ∈ V^n`, then `β_{x_i} = b_j` for every `x_i ∈ C`. Put
`E_{pq} = {x ∈ C : ε(x) = p, ε(a_i x) = q}`. On `E_{00}, E_{11}, E_{01}, E_{10}` the element `β_x`
equals `a_j`, `s a_j s^{-1}`, `s a_j`, `a_j s^{-1}` respectively.
- `E_{00} ∪ E_{01} = C(0)` and `E_{10} ∪ E_{11} = C(1)` are nonempty.
- If two of the sets are nonempty and they share an index (`E_{00}, E_{01}`; `E_{10}, E_{11}`;
  `E_{00}, E_{10}`; `E_{01}, E_{11}`), the corresponding values give respectively `a_j = s a_j`,
  `s a_j s^{-1} = a_j s^{-1}`, `a_j = a_j s^{-1}`, `s a_j = s a_j s^{-1}`, each forcing `s = 1`.
- So either only `E_{00}, E_{11}` are nonempty, i.e. `a_i C(0) ⊆ C(0)`, `a_i C(1) ⊆ C(1)`, hence
  `a_i` fixes both (it is a bijection), and `a_j = s a_j s^{-1}`; or only `E_{01}, E_{10}` are
  nonempty, `a_i` swaps `C(0)` and `C(1)`, and `s a_j = a_j s^{-1}`, i.e. `a_j^{-1} s a_j = s^{-1}`.

Conversely, in either case `β_x` is constant, so `t h t^{-1} ∈ V^n`. This proves the key
computation. Note that `h ∈ t^{-1} V^n t` if and only if `t h t^{-1} ∈ V^n`.

**Step 3 (item 2).** Let `h = (a_1, ..., a_n) ∈ F` and fix `j`, with `i = i(j)`. The alternative in
Step 2 is decided by `a_i` alone, so it is the same for all `s ∈ S`.
- *Case "fixes".* `a_j` commutes with every `s ∈ S`, hence with all of `V`. By
  `thompson-v-finitely-presented-infinite-simple`, `V` is infinite and simple, hence nonabelian, and
  its centre is a proper normal subgroup, hence trivial. So `a_j = 1`.
- *Case "swaps".* `a_j^{-1} s a_j = s^{-1}` for all `s ∈ S`. If `a, a'` both satisfy this, then
  `a^{-1} s a = a'^{-1} s a'`, so `a a'^{-1}` commutes with every `s ∈ S`, hence is `1`. So at most
  one element `c_j ∈ V` can occur.

Thus `a_j ∈ {1, c_j}` for each `j`, and `|F| ≤ 2^n`. `S` exists since `V` is finitely generated.

**Step 4 (item 3).** Let `α_1, ..., α_r` be the automorphisms `Ad(t^{-1}) ∘ α_σ`, with `σ` over all
permutations and `t` over `{1}` and the shears of item 2. Since `Ad(t^{-1})` is a bijection,

```text
⋂_{t} ⋂_{σ} Ad(t^{-1})(α_σ(T_n)) = ⋂_{t} t^{-1} ( ⋂_σ α_σ(T_n) ) t = ⋂_{t} t^{-1} V^n t = F
```

by item 1, which is finite by item 2. ∎
