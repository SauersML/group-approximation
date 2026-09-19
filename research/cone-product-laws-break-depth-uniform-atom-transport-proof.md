---
rg: 2
id: cone-product-laws-break-depth-uniform-atom-transport-proof
kind: route
title: "Take the Bernoulli cone-product law of an irrational point-mass-corrected Lebesgue character, bound its Koopman defect by Hellinger ≤ TV, and read the atom at [0^d] off the prefixes of 0^d"
target: cone-product-laws-break-depth-uniform-atom-transport
requires: []
---

Notation is as in the target. Words are finite 0-1 strings, `|w|` is the length, `[w]` is the cone.
`ι_w : C → [w]` is `ι_w(x) = wx`. The group `Â = Hom(A, R/Z)` is written additively. `V` acts on `A`
by `(h·k)(x) = k(h^{−1}x)` and on `Â` by `(h·χ)(k) = χ(k∘h)`. Then `(h·χ)(h·k) = χ(k)`. `A_d` is the
set of `k ∈ A` that are constant on every cone of depth `d`, and `A = ∪_d A_d`.

## Step 1. The seed character

Let `λ` be the uniform Bernoulli measure on `C` and `x* = 1^∞`. Define

  `ξ(k) = √2·(∫ k dλ − k(x*))  mod 1`.

This is a homomorphism `A → R → R/Z`, so `ξ ∈ Â`. It satisfies:
- `ξ(1_C) = √2·(1 − 1) = 0`, and so `ξ(c·1_C) = 0` for every `c ∈ Z`;
- for `m ≥ 1`, `x* ∉ [0^m]`, so `ξ(1_{[0^m]}) = √2·2^{−m}`.

## Step 2. The random character

For a word `w`, set `ξ_w(k) = ξ(k∘ι_w)`. This is again in `Â`. Suppose `k ∈ A_d` and `|w| ≥ d`.
Then `k∘ι_w` is constant, so `ξ_w(k) = 0` by Step 1.

Fix `p ∈ (0,1)`. Let `S` be a random set of words that contains each word independently with
probability `p`. Define

  `χ_S(k) = Σ_{w ∈ S} ξ_w(k)`.

For `k ∈ A_d`, only the finitely many `w ∈ S` with `|w| < d` contribute. So the sum is finite, and it
is additive in `k`. Hence `χ_S ∈ Â`, and `S ↦ χ_S` is Borel for the product topology on `Â`. Let `ν_p`
be the law of `χ_S`.

Since `ξ_w(1_C) = ξ(1_C) = 0` for every `w`, we get **`χ_S(1_C) = 0` for every `S`**.

## Step 3. Transport by an element of V (coupling)

Let `h ∈ V` have a tree-pair diagram with `n` leaves, domain leaves `a_1, …, a_n` and range leaves
`b_1, …, b_n`, so that `h(a_i x) = b_i x`. Let `I_D` and `I_R` be the internal nodes of the domain
and range trees. Each has `n − 1` elements. Every word either lies in `I_D` or has the form `a_i w'`
(with `w'` possibly empty), and never both. The same holds for the range tree.

For `w = a_i w'` we have `h∘ι_w = ι_{b_i w'}`. So `h·ξ_w = ξ_{ĥ(w)}`, where
`ĥ(a_i w') = b_i w'`. The map `ĥ` is a bijection from the words outside `I_D` onto the words outside `I_R`.

Take `S` as in Step 2 and an independent Bernoulli(`p`) subset `S''` of `I_R`. Put
`S' = ĥ(S \ I_D) ∪ S''`. Then `S'` again contains each word independently with probability `p`,
so `χ_{S'} ~ ν_p`. On the event `E = {S ∩ I_D = ∅, S'' = ∅}` we have
`h·χ_S = Σ_{w∈S} ξ_{ĥ(w)} = χ_{S'}`. The law of `h·χ_S` is `h_*ν_p`. Hence

  `‖h_*ν_p − ν_p‖ ≤ 2·P(E^c) ≤ 4p(n − 1)`,

in the total-variation norm `‖α − β‖ = ∫ |dα − dβ|`.

## Step 4. The representation and the vector

Since `V` is countable, fix weights `c_h > 0` with `Σ_h c_h = 1` and put `ν̄ = Σ_{h∈V} c_h h_*ν_p`.
Each `g_*ν̄ = Σ_h c_h (gh)_*ν_p` is equivalent to `ν̄`. On `H = L²(Â, ν̄)` set
- `(π(k)F)(χ) = e(χ(k)) F(χ)` for `k ∈ A`, where `e(t) = exp(2πit)`;
- `(π(h)F)(χ) = (dh_*ν̄/dν̄)^{1/2}(χ) · F(h^{−1}·χ)` for `h ∈ V`.

Both are unitary. `h ↦ π(h)` is a representation by the chain rule for Radon–Nikodym derivatives.
Also `π(h)π(k)π(h)^{−1}` is multiplication by `e((h^{−1}·χ)(k)) = e(χ(k∘h^{−1})) = e(χ(h·k))`, which
is `π(h·k)`. So `(k, h) ↦ π(k)π(h)` is a unitary representation `π_p` of `G = A ⋊ V`.

Let `f_p = (dν_p/dν̄)^{1/2}`. Then `‖f_p‖ = 1` and `⟨π(k)f_p, f_p⟩ = ∫ e(χ(k)) dν_p(χ)`. So the
`A`-spectral law of `f_p` is exactly `μ_p = ν_p`. By Step 2, `χ(1_C) = 0` holds `ν_p`-a.s., so
`π(1_C)f_p = f_p`. This is item 3 of the theorem.

## Step 5. The defect

*Elements of `V`.* A change of variables gives `π(h)f_p = (dh_*ν_p/dν̄)^{1/2}`. Use
`(√a − √b)² ≤ |a − b|` for `a, b ≥ 0`, and then Step 3:

  `‖π(h)f_p − f_p‖² = ∫ ((dh_*ν_p/dν̄)^{1/2} − (dν_p/dν̄)^{1/2})² dν̄ ≤ ‖h_*ν_p − ν_p‖ ≤ 4p(n_h − 1)`.

*The generators `±1_{[0]}`.* Take `w ∈ S`. If `w = ∅`, then `1_{[0]}∘ι_w = 1_{[0]}` and
`ξ(1_{[0]}) = √2/2`. If `w` starts with `0`, then `1_{[0]}∘ι_w = 1_C`, contributing `0`. If `w`
starts with `1`, then `1_{[0]}∘ι_w = 0`. So `χ_S(1_{[0]}) = (√2/2)·1[∅ ∈ S]`, and

  `‖π(±1_{[0]})f_p − f_p‖² = p·|e(√2/2) − 1|² ≤ 4p`.

Hence `ε(f_p) ≤ 2·max(1, N_S − 1)^{1/2}·√p = c_S √p`. This is item 1.

## Step 6. The atom at depth d

Fix `d ≥ 1` and a word `w`. We compute `1_{[0^d]}∘ι_w`, which is the function `x ↦ 1_{[0^d]}(wx)`.
- If `w = 0^j` with `j < d`, it is `1_{[0^{d−j}]}`. By Step 1 the contribution is `√2·2^{−(d−j)}`.
- If `w = 0^j` with `j ≥ d`, it is `1_C`, and the contribution is `0`.
- If `w = 0^j 1 w''` with `j < d`, then `wx ∉ [0^d]` for every `x`, so the function is `0`.
- If `w = 0^j 1 w''` with `j ≥ d`, then `wx ∈ [0^d]` for every `x`, so the function is `1_C`,
  contributing `0`.

Therefore, with `J = {j < d : 0^j ∈ S}`,

  `χ_S(1_{[0^d]}) = √2 · q_J mod 1`, where `q_J = Σ_{j∈J} 2^{−(d−j)}`.

If `J = ∅`, this is `0`. If `J ≠ ∅`, then `q_J` is a rational number in `(0, 1)`, so `√2·q_J` is
irrational and in particular not an integer. Hence `χ_S[0^d] = 0` holds exactly when none of the
`d` words `0^0, 0^1, …, 0^{d−1}` lies in `S`, and

  `μ_p{χ[0^d] = 0} = (1 − p)^d`.

This is item 2. For `d = 1` it gives `μ_p{χ[[0]] = 0} = 1 − p`.

## Step 7. The corollary and the quantitative form

Suppose `K_0` were absolute. Take `p ≤ 1/10` and `d = ⌈1/p⌉ ≥ 2`, so `U = [0^d]` is proper. Then
`(1 − p)^d ≤ e^{−pd} ≤ e^{−1}`, and

  `μ_p{χ[[0]]=0} − μ_p{χ[U]=0} ≥ 1 − p − e^{−1} ≥ 0.53`,

whereas `K_0·ε(f_p) ≤ K_0 c_S √p`. This is `< 0.53` once `p < (0.53/(K_0 c_S))²`, a contradiction.

For the quantitative form, fix `ε ∈ (0, c_S)` and take `p = ε²/c_S²`. Then `ε(f_p) ≤ ε`, and

  `(1−p) − (1−p)^d = (1−p)(1 − (1−p)^{d−1}) ≥ (1−p)(1 − e^{−p(d−1)})`,

which is the stated lower bound on `F(ε, d)` when `F` is nondecreasing in `ε`.

## Remark: the restricted statement

Let `H' = ker(π(1_C) − 1)^⊥`. It is `G`-invariant because `1_C` is central. Suppose `(G, Z·1_C)` has
relative (T) with Kazhdan pair `(Q, κ)`, and let `L = max_{q∈Q} |q|_S`. For a unit `ξ ∈ H'`, the
subrepresentation on `H'` has no `1_C`-invariant vector. So some `q ∈ Q` has
`‖π(q)ξ − ξ‖ ≥ κ`, and telescoping gives `ε(ξ) ≥ κ/L`. Then
`|μ{χ[U]=0} − μ{χ[[0]]=0}| ≤ 1 ≤ (L/κ)·ε(ξ)`. So relative (T) implies the restricted statement.
The vectors `f_p` all lie in `ker(π(1_C) − 1)`, so they say nothing about the restricted statement.
