---
rg: 2
id: mapping-torus-radical-is-pseudo-orbit-recurrence-proof
kind: route
title: Conjugate an MF approximation by powers of the image of t to get a chain; close a long chain by pigeonhole in U(d)^S and wrap it with the cyclic block shift
target: mapping-torus-radical-is-pseudo-orbit-recurrence
requires: []
---

Notation is that of the claim. `Rad_MF(G)` is the intersection of the kernels of `Pi'`, over MF
approximations `Pi = (pi_n : G -> U(k_n))`, where `Pi'` is the induced homomorphism into the unitary
group of `Q = prod M_(k_n) / (+) M_(k_n)` and `‖[x_n]‖_Q = limsup ‖x_n‖`. For a word `v` and an
approximation, `v(pi_n)` is the product of the `pi_n(s)^(±1)`.

**Step 0 (words).** Let `Pi` be an MF approximation. Then `pi_n(1)` is a unitary with
`‖pi_n(1)^2 − pi_n(1)‖ -> 0`, so `pi_n(1) -> 1`, and `‖pi_n(s^-1) − pi_n(s)^-1‖ -> 0`. Hence for
every fixed word `v`, `‖v(pi_n) − pi_n(v)‖ -> 0` by finitely many applications of approximate
multiplicativity. In particular `‖r(pi_n) − 1‖ -> 0` for every relator `r` of the presentation.

**Step 1 (1 ⇒ 2).** Let `g ∉ Rad_MF(G)`, witnessed by `Pi`, and put `4δ = ‖Pi'(g) − 1‖ > 0`.
Fix `ε > 0`, and choose `n` with `‖g(pi_n) − 1‖ ≥ δ` and, by Step 0, with
`‖r(pi_n) − 1‖ ≤ ε` for `r ∈ R_0` and `‖T pi_n(s) T^-1 − w_s(pi_n)‖ ≤ ε` for `s ∈ S`, where
`T = pi_n(t)` and `d = k_n`. Put `b_j(s) = T^j pi_n(s) T^-j` for `j ∈ N`. Conjugation by `T^j`
is a `*`-automorphism, so `v(b_j) = T^j v(pi_n) T^-j` for every word `v`. Therefore:
- `‖r(b_j) − 1‖ = ‖r(pi_n) − 1‖ ≤ ε` and `‖g(b_j) − 1‖ = ‖g(pi_n) − 1‖ ≥ δ`;
- `‖b_(j+1)(s) − w_s(b_j)‖ = ‖T pi_n(s) T^-1 − w_s(pi_n)‖ ≤ ε`.

So `(b_j)` is an infinite `(ε, δ)`-chain in dimension `d`.

**Step 2 (2 ⇒ 3, 2 ⇔ 4).** An infinite chain has initial segments of every length, so 2 gives 3.
For 4 ⇒ 2, pick `b_0 ∈ Y` and, inductively, `b_(j+1) ∈ Y` with `‖b_(j+1) − W_d(b_j)‖ ≤ ε`. For
2 ⇒ 4, let `Y` be the closure of `{b_j}`, which lies in the closed set `Q_ε ∩ N_δ(g)`. If
`y = lim b_(j_k)`, then `W_d(y) = lim W_d(b_(j_k))` by continuity, and each `W_d(b_(j_k))` lies
within `ε` of `b_(j_k + 1) ∈ Y`. Since `Y` is compact, `Y_ε` is closed, and `W_d(y) ∈ Y_ε`.

**Step 3 (closing, from 3).** Let `b_0, ..., b_L` be an `(ε, δ)`-chain with `L + 1 > N(d, ε)`.
Two of its points lie in one closed `ε`-ball, so there are `i < j` with `‖b_i − b_j‖ ≤ 2ε`.
Put `m = j − i ≥ 1` and `c_l = b_(i+l)` for `l ∈ Z/m`. Then `‖c_(l+1) − W_d(c_l)‖ ≤ ε` for
`l ≠ m − 1`, and at the wrap
`‖c_0 − W_d(c_(m−1))‖ ≤ ‖b_i − b_j‖ + ‖b_j − W_d(b_(j−1))‖ ≤ 3ε`.

**Step 4 (the block shift).** On `H = (C^d)^(Z/m)` put `pi(s) = ⊕_l c_l(s)` and
`(T ξ)_l = ξ_(l+1)`. Then `T^-1 ξ = η` with `η_(l+1) = ξ_l`, and
`(T pi(s) T^-1 ξ)_l = c_(l+1)(s) ξ_l`. So `T pi(s) T^-1 − w_s(pi)` is block diagonal with blocks
`c_(l+1)(s) − w_s(c_l)`, and it has norm at most `3ε`. Also `r(pi) = ⊕ r(c_l)`, within `ε` of `1`
for `r ∈ R_0`, and `‖g(pi) − 1‖ = max_l ‖g(c_l) − 1‖ ≥ δ`.

**Step 5 (3 ⇒ 1).** Apply Steps 3 and 4 with `ε = 1/n`. This gives `pi_n : S ∪ {t} -> U(k_n)` in
which every relator of the finite presentation of `G` is within `3/n` of `1`, and
`‖g(pi_n) − 1‖ ≥ δ`. For each `x ∈ G` fix a word `v_x` and put `pi'_n(x) = v_x(pi_n)`. The word
`v_x v_y v_(xy)^-1` is trivial in `G`, hence a fixed finite product of conjugates of relators, so
`‖pi'_n(x) pi'_n(y) − pi'_n(xy)‖ = O(1/n)`. Thus `Pi = (pi'_n)` is an MF approximation of `G`
with `‖Pi'(g) − 1‖ ≥ limsup ‖g(pi_n) − 1‖ − 0 ≥ δ` (the words `v_g` and `g` agree in `G`, so their
values differ by `O(1/n)`). Hence `g ∉ Rad_MF(G)`.

**Step 6 (covering number).** `X_d` is compact, so `N(d, ε)` is finite. The bound
`(C/ε)^(|S| d^2)` for small `ε` follows from the covering estimate for `U(d)`, a compact Lie group
of real dimension `d^2`, in operator norm (Szarek), taken to the power `|S|`. Only finiteness is
used in Steps 3 to 5.

**Corollary.** Negate 3 for each `g ∈ K \ {1}` and each `δ`, and use 3 ⇔ 4. Also
`Rad_MF(G) ⊆ K`, because `G/K = Z` is MF. So `Rad_MF(G) = K` is exactly the witness form.
