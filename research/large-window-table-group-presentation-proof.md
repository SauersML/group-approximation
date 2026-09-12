---
rg: 2
id: large-window-table-group-presentation-proof
kind: route
title: Express every table generator through the letters, triangulate each relator inside the decoder ball, and invert evaluation
target: large-window-table-groups-present-the-ambient-group
requires: []
artifacts:
  - research/artifacts/thompson-v-window-screen-2026-09-12.md
---

Notation as in the target. Balls are word-metric balls in `X`, and `|g|` is the
word length.

1. **Evaluation.** Every relator of `U` is an equality in `G`. So `pi(x_a) = a`
   defines a homomorphism `pi: U -> G`.

2. **The letters generate `U`.** Since `r_s, r_m >= 1`, `X` lies in `S` and in `M`.
   - **Inverses.** For `g` in `X`, the pairs `(g^-1, g)` and `(1, 1)` of `S x M`
     have equal products, so `x_(g^-1) = x_g^-1`.
   - **Prefix lemma.** Let `g_1 ... g_c` be any word in `X` with `c <= r_s`, not
     necessarily geodesic, and put `p_i = g_1 ... g_i`. Each `p_i` has length at
     most `i <= r_s`, so it lies in `S`.
     - The pairs `(p_(i-1), g_i)` and `(p_i, 1)` of `S x M` have equal products, so
       `x_(p_(i-1)) x_(g_i) = x_(p_i)`.
     - By induction, `x_(g_1) ... x_(g_c) = x_(p_c)`.
   - **Balls.** Every `b` in `S` is the value of a geodesic word of length at most
     `r_s`. By the prefix lemma, `x_b` is a word in the letters `x_g`, `g` in `X`.
   - **Powers of `h`.** `h` lies in `S`, since `|h| <= r_s`. For `j >= 1` the
     symmetry relator with `k = h` and `m = h^j` gives `x_h x_(h^j) = x_(h^(j+1))`.
     So `x_(h^j) = x_h^j`.
   - **The rest of `M`.** Let `a = k b` with `k` in `<h>` and `b` in `B_(r_m)(X)`.
     Then `b` lies in `S`, since `r_m <= r_s`, and the symmetry relator
     `x_k x_b = x_(kb)` expresses `x_a`.

3. **Relators hold on the letters.** Take the presentation on a subset `X_0`
   with `X = X_0 u X_0^-1`, so the letter for `g^-1` is `x_g^-1`, matching the
   inverse step. Let `r = g_1 ... g_l` be in `R`, with `l <= L`. Put
   `c = ceil(l/2)`.
   - Since `r = 1` in `G`, the words `u = g_1 ... g_c` and
     `w = g_l^-1 ... g_(c+1)^-1` evaluate to the same element `e`.
   - Both have length at most `ceil(L/2) <= r_s`.
   - By the prefix lemma, `x_(g_1) ... x_(g_c) = x_e` and
     `x_(g_l^-1) ... x_(g_(c+1)^-1) = x_e`.
   - By the inverse step, `x_(g_(c+1)) ... x_(g_l) = (x_(g_l^-1) ... x_(g_(c+1)^-1))^-1 = x_e^-1`.

   So `x_(g_1) ... x_(g_l) = x_e x_e^-1 = 1` in `U`.

4. **Inverse map.** By step 3, `g -> x_g` defines a homomorphism `iota: G -> U`.
   - `iota` is onto by step 2.
   - `pi iota` fixes each `g` in `X`, so `pi iota = id_G`, and `iota` is injective.

   So `iota` is an isomorphism with inverse `pi`. QED

**Corollary.**
1. Let `psi: U -> K` with `K` finite. Then `psi iota` is a homomorphism from `G`
   to a finite group, which is trivial because `G` has no nontrivial finite
   quotient. So `psi(x_h) = psi(iota(h)) = 1`.
2. If `G` is simple, a homomorphism `G -> K` that does not kill `h` has trivial
   kernel, so it is an embedding.
3. An automaton over a subgroup induces one over the group with the same
   injectivity and surjectivity (the ascent used in
   `thompson-v-nonsurjunctivity-ascends-to-leavitt-units`). So a surjunctive `K`
   containing `G` makes `G` surjunctive.
