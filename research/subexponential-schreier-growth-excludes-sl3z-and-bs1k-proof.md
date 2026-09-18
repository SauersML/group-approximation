---
rg: 2
id: subexponential-schreier-growth-excludes-sl3z-and-bs1k-proof
kind: route
title: Count the orbit of a distorted element inside a small Schreier ball
target: subexponential-schreier-growth-excludes-sl3z-and-bs1k
requires: []
---

Throughout, `G` acts faithfully on `X`, `S ⊂ G` is finite, and word lengths and
balls are as in the claim. The function `γ_S` is nondecreasing.

**Item 1.** Let `g ∈ ⟨S⟩` have infinite order and fix `M >= 1`.

- If every `g`-orbit in `X` had at most `M` points, then `g^{M!}` would fix every
  point. Faithfulness would then force `g^{M!} = 1`, a contradiction.
- So some `x` has a `g`-orbit with more than `M` points. The points
  `x, g x, …, g^M x` are then pairwise distinct.
- Each `g^j x` lies in `B_S(x, |g^j|_S) ⊂ B_S(x, R_M)`.

Hence `γ_S(R_M) >= |B_S(x, R_M)| >= M + 1`.

**Item 2, SL_3(Z).**

- *Conjugation.* Let `U = {I + aE_12 + bE_13}`, which is isomorphic to `Z^2` via
  `(a, b)`. Since `D^-1 e_1 = e_1`, we get `D^-k (I + e_1 w) D^k = I + e_1 (w D^k)`.
  So conjugating by `D^k` acts on `(a, b)` by `(a, b) ↦ (a, b) A^k`. It follows
  that `D^-k x_12 D^k = (F_{2k+1}, F_{2k})` and
  `D^-k x_13 D^k = (F_{2k}, F_{2k-1})`, with `F_1 = F_2 = 1`.
- *Commutator.* For `u = I + aE_12 + bE_13`,
  `u x_23 u^-1 = I + E_23 + aE_13`, and so `[u, x_23] = I + aE_13 = x_13^a`.
- *Zeckendorf word.* Let `N >= 1` and write the Zeckendorf expansion
  `N = Σ_{i=1}^m F_{j_i}`, with indices `j_i >= 2` that are pairwise
  non-consecutive.
  - Put `u_i = x_12` and `k_i = (j_i − 1)/2` if `j_i` is odd, and `u_i = x_13` and
    `k_i = j_i/2` if `j_i` is even.
  - The `k_i` are distinct: equal `k` would need `j = 2k` and `j' = 2k + 1`, which
    are consecutive. Order them increasingly.
  - The product `Π_i D^-k_i u_i D^k_i` lies in `U` and has first coordinate `N`.
    As a word it is
    `w_N = D^-k_1 u_1 D^{k_1−k_2} u_2 ⋯ D^{k_{m−1}−k_m} u_m D^{k_m}`, of length
    `2k_m + m`.
- *Length bound.* Since `F_j >= φ^{j−2}`, we have `j_m <= log_φ N + 2`. Also
  `k_m <= j_m/2` and `m <= j_m/2`. So `x_13^N = [w_N, x_23]` has length at most
  `2(2k_m + m) + 2 <= 3 j_m + 2 <= 3 log_φ N + 8`. For `N < 0`, invert.

The script `experiments/gl-n-z-2v-orbit-growth-2026-09-17/sl3z_root_distortion_words.py`
checks these words exactly.

**Item 2, BS(1,k).**

- Since `t x^d t^-1 = x^{kd}`, induction on `L` gives
  `x^{d_0} t x^{d_1} t ⋯ t x^{d_L} t^-L = x^{Σ d_s k^s}`.
- Every integer `N` has a base-`k` expansion with digits `0 <= d_s <= |k| − 1`
  and `L + 1 <= log_{|k|}|N| + 3` digits. For `k > 0` this covers `N >= 0`, and
  `N < 0` follows by inverting. For `k < 0` it is the negative-base expansion,
  where a leading digit in position `L` forces
  `|N| >= |k|^L − (|k| − 1)(|k|^{L−1} + |k|^{L−3} + ⋯) >= |k|^{L−1}·|k|/(|k|+1)`.
- The word has length at most `(L+1)(|k| − 1) + 2L <= (L+1)(|k| + 1)`, which is
  at most `(|k| + 1)(log_{|k|}|N| + 3)`.

**Item 2, H_3(Z).**

- Centrality gives `c^{m^2} = [a^m, b^m]`, as in
  `heisenberg-in-nv-forces-drift-free-central-element-proof`, item 2.
- For `N >= 1`, write `N = m^2 + r` with `m = ⌊sqrt N⌋` and `0 <= r <= 2m`.
- Then `c^N = [a^m, b^m] c^r` has length at most `4m + 4r <= 12m <= 12 sqrt N`.

**Item 3.** Suppose `H <= G` is isomorphic to one of the groups, and let
`T ⊂ H` be the image of the generators above. `H` acts faithfully on `X` by
restriction, and `γ_T` is part of the hypothesis, because the growth conditions
quantify over every finite subset of `G`. Let `g` be the image of the distorted
element (`x_13`, `x`, or `c`).

- *SL_3(Z) and BS(1,k).*
  - Item 2 gives `R_M <= A log M + B` for constants `A, B > 0`.
  - For large `R`, put `M = ⌊exp((R − B)/A)⌋`. Then `R_M <= R`, and item 1 gives
    `γ_T(R) >= M + 1 > exp((R − B)/A)`.
  - So `liminf (1/R) log γ_T(R) >= 1/A > 0`, which contradicts subexponential
    growth.
  - `SL_d(Z)` and `GL_d(Z)` with `d >= 3` contain `SL_3(Z)` as a block, so they
    are excluded as well.
- *H_3(Z).*
  - For `R >= 24`, put `M = ⌊((R − 12)/12)^2⌋ >= 1`. Then
    `R_M <= 12 sqrt M + 12 <= R`, so `γ_T(R) >= M + 1 > (R − 12)^2 / 144`.
  - Hence `γ_T(R)/R^2 >= 1/576` for all `R >= 24`, which contradicts
    subquadratic growth.
- *Linear growth.*
  - If `γ_S(R) <= C(R + 1)`, item 1 gives `R_M >= (M + 1)/C − 1`.
  - If the stable length `τ = inf_n |g^n|_S / n` were `0`, pick `n_0` with
    `|g^{n_0}|_S <= ε n_0`. Then `|g^j|_S <= ε j + max_{r<n_0} |g^r|_S` for all
    `j`, so `R_M <= εM + C_ε`.
  - For `ε < 1/C` this contradicts the lower bound, so `τ > 0`.

**Item 4.**

- *Growth bound.* For `f ∈ [[X, T]]`, the cocycle `c_f` is continuous from a
  compact space into the discrete group `Z^d`, so it takes finitely many values.
  Put `K_S = max_{s∈S} max_x |c_s(x)|_∞`.
  - From `c_{fg}(x) = c_f(g x) + c_g(x)` and `c_{f^-1}(x) = −c_f(f^-1 x)`, a word
    `w` of length `r` satisfies `w x = T^v x` with `|v|_∞ <= r K_S`.
  - Hence `B_S(x, R) ⊂ {T^v x : |v|_∞ <= K_S R}`, which has at most
    `(2 K_S R + 1)^d` points. This is polynomial, hence subexponential. For
    `d = 1` it is linear, hence subquadratic.
- *Faithfulness.* The action is faithful, because the elements are
  homeomorphisms of `X`.
- *Conclusion.* Item 3 applies. `[[{0,1}^Z]]` is the case `d = 1` with `T` the
  shift, so it contains no `H_3(Z)`, and hence no `SL_n(Z)` or `GL_n(Z)` with
  `n >= 3`. ∎
