---
rg: 2
id: bounded-depth-operator-groups-contain-every-fg-group-proof
kind: route
title: Enumerate the group by word length, match the enumeration to a nested basis of the Cantor module, and let the group act by left translation
target: bounded-depth-operator-groups-contain-every-fg-group
requires: []
---

## Step 1: a nested basis

Let `β_0 = 1`. For `i ≥ 1` write `i = 2^j + r` with `0 ≤ r < 2^j`, and let `β_i = 1_[w_i 1]`, where `w_i` is the
`r`-th word of length `j` in lexicographic order. Then `{β_i : i < 2^k}` is a basis of `V_k` for every `k ≥ 0`.

*Proof.* There are `2^k` such vectors, all in `V_k`, and `dim V_k = 2^k`. They span `V_k` by induction on `k`: if
they span `V_{k−1}`, then for `|w| = k − 1` both `1_[w]` and `1_[w1]` lie in the span, so `1_[w2] = 1_[w] − 1_[w1]`
does too. So all cylinders of length `k` lie in the span. ∎

## Step 2: a length-respecting enumeration

Let `G` be infinite with finite symmetric generating set `S`. (A finite group embeds in `V ⊂ BDep_1(K)`.) Put
`|·| = |·|_S` and `B(r) = {g : |g| ≤ r}`. Enumerate `G = {g_0 = e, g_1, g_2, ...}` so that `|g_i|` is nondecreasing.
Let `W_k = {g_i : i < 2^k}`.

**Absorption.** If `Y ⊂ B(r)` and `|B(r)| ≤ 2^m`, then `Y ⊂ W_m`, because the enumeration lists all of `B(r)` before
any element of length `> r`.

## Step 3: the action and its depth shift

Define `π(g)` on the basis by `π(g) β_i = β_j` where `g g_i = g_j`, and extend linearly. It is a permutation of a
basis, so it is invertible, and `π` is a homomorphism because left translation is an action. It is faithful because
`π(g) β_0 = β_j` with `g_j = g`.

Fix `g` with `|g| = ℓ` and `k ≥ 1`. Let `ρ = |g_{2^k − 1}| ≥ 1` be the largest length in `W_k`. (For `k = 0`,
`g W_0 = {g} ⊂ B(ℓ)` and `|B(ℓ)| ≤ (|S|+1)^ℓ`, so absorption applies directly.)

- `B(ρ − 1) ⊂ W_k`, so `|B(ρ − 1)| ≤ 2^k`.
- `g W_k ⊂ B(ρ + ℓ)`. Balls are submultiplicative, `B(x + y) = B(x) B(y)`, so
  `|B(ρ + ℓ)| ≤ |B(ρ − 1)|·|B(ℓ + 1)| ≤ 2^k (|S| + 1)^(ℓ+1)`.
- Put `c = ⌈(ℓ + 1) log₂(|S| + 1)⌉`. By absorption, `g W_k ⊂ W_{k+c}`.

Now let `f ≠ 0` have depth `k`. By Step 1, `f` is a combination of `β_i` with `i < 2^k`. So `π(g) f` is a
combination of `β_j` with `g_j ∈ g W_k ⊂ W_{k+c}`, which lies in `V_{k+c}`. Hence `s(π(g)) ≤ c`. The same bound
holds for `g^{-1}`, since `|g^{-1}| = ℓ`. So `π(G) ⊂ BDep_1(K)`.

**Countable groups.** Every countable group embeds in a 2-generated group (Higman--Neumann--Neumann), so it embeds
in `BDep_1(K)`.

**Every `d`.** `V_k(X^d) = V_k(X)^{⊗d}`, and `T ↦ T ⊗ 1 ⊗ ⋯ ⊗ 1` maps `V_k(X)^{⊗d}` into
`V_{k+s(T)}(X) ⊗ V_k(X)^{⊗(d−1)} ⊂ V_{k+s(T)}(X^d)`. So it is a faithful homomorphism `BDep_1(K) → BDep_d(K)`
with `s(T ⊗ 1) ≤ s(T)`.

## Step 4: the Baumslag--Gersten image

Take `G = BG` and `A = π(a)`. By subadditivity of `s`, and since `s(π(x)) ≤ C` for `x ∈ S`,
`E_A(n) ≤ C·|a^n|_BG`. The tower relation of `depth-distortion-power-conjugates-leavitt-hosts-proof`, Step 3,
gives `E_A(N_i) ≤ C'·2^i`.

`π` is faithful and `K = F_q` is finite. By Step 4d of that proof, `A` is not locally periodic, so
`E_A(n) → ∞`. The pointwise statement DG would give `E_A(n) ≥ α log^{(j)} n` for large `n`, and Step 3 of that
proof shows this contradicts the tower bound. So DG fails in `BDep_1(F_q)`.

(Directly: in `π`, the orbit of `β_0` under `<A>` is `{β_j : g_j = a^n}`, which is infinite.)

## Step 5: the dead class

Suppose an argument shows `BG ⊄ H` for a Leavitt host `H ⊂ BDep_d(F_q)` using only properties of the image that are
defined for every subgroup of `BDep_d(F_q)` and inherited by subgroups: the filtration `(V_k)`, the depth shifts
`s(T^{±n})`, and conjugation inside `BDep_d(F_q)`. Then the same argument shows `BG ⊄ BDep_d(F_q)`, contradicting
Step 3. So it breaks at some step, and by Step 4 the first failing statement is a regularity claim about divergent
depth profiles.

For `H_3(Z)` and `BS(1,k)`, Step 3 applies verbatim, and their distorted central or base elements get images
with sublinear `E` and zero depth rate.
