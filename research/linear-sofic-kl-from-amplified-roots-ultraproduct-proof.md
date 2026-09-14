---
rg: 2
id: linear-sofic-kl-from-amplified-roots-ultraproduct-proof
kind: route
title: Push the linear sofic representation to the extension field, amplify coordinatewise, and read the approximate roots as an exact root in the rank ultraproduct
target: linear-sofic-kl-from-amplified-algebraic-roots
requires: []
artifacts:
  - research/artifacts/ideas-nonhyperlinear-2026-09-13.md
---

Fix `F <= L` with `ARR(L)`, a countable `F`-linear sofic group `G` with
linear sofic representation `Theta : G --> P = Pi_{i -> omega} GL_{n_i}(F)/d_omega`,
and `w` in `G * <t>` with exponent sum `m != 0`. Only finitely many
coefficients `g_1, ..., g_k` occur in `w`, so `w = v(t ; g_1, ..., g_k)` for a
word `v` in `F_k * <t>` with exponent sum `m`.

1. **Field extension.** The rank of a matrix is the largest size of a
   nonvanishing minor, so it does not change when `F` is enlarged to `L`.
   Hence the coordinatewise inclusions `GL_{n_i}(F) <= GL_{n_i}(L)` preserve
   `rho(x - 1)` and induce an injective homomorphism
   `iota : P --> P_L = Pi_{i -> omega} GL_{n_i}(L)/d_omega`.
2. **Coordinatewise amplification.** For integers `r_i >= 1` the maps
   `x |-> x (x) 1_{r_i}` are group homomorphisms
   `GL_{n_i}(L) --> GL_{n_i r_i}(L)`, and
   `rank((x (x) 1_r) - 1) = rank((x - 1) (x) 1_r) = r rank(x - 1)`, so
   `rho` is preserved. They induce an injective homomorphism
   `Phi : P_L --> Q = Pi_{i -> omega} GL_{n_i r_i}(L)/d_omega` for any
   choice of `(r_i)`.
3. **Roots.** Choose representatives `Theta(g_j) = [(a_{j,i})_i]` with
   `a_{j,i}` in `GL_{n_i}(F)`. For each `i` apply `ARR(L)` to the tuple
   `(a_{1,i}, ..., a_{k,i})`, the word `v`, and `epsilon = 1/i`. This gives
   `r_i` and `T_i` in `GL_{n_i r_i}(L)` with
   `rho(v(T_i ; a_{j,i} (x) 1_{r_i}) - 1) <= 1/i`. Use these `r_i` in step 2.
4. **Exactness in the ultraproduct.** Put `Theta' = Phi o iota o Theta`,
   injective, and `tau = [(T_i)_i]` in `Q`. The quotient map
   `Pi GL_{n_i r_i}(L) --> Q` is a homomorphism, and `(a_{j,i} (x) 1_{r_i})_i`
   represents `Theta'(g_j)`. So `v(tau ; Theta'(g_1), ..., Theta'(g_k))` is
   represented by `(v(T_i ; a_{j,i} (x) 1_{r_i}))_i`, whose distance to `1` is
   `lim_omega rho(v(T_i ; ...) - 1) <= lim_omega 1/i = 0`. Thus
   `w(tau) = 1` in `Q`.
5. **Conclusion.** The homomorphism `G * <t> --> Q` with `g |-> Theta'(g)` and
   `t |-> tau` kills `w`, so it factors through `G_w = (G * <t>)/<<w>>`. The
   composite `G --> G_w --> Q` is `Theta'`, which is injective; hence
   `G --> G_w` is injective.

Nothing in the argument uses `m != 0` except through the premise; the premise
is where nonsingularity enters.
