---
rg: 2
id: matricially-stable-overgroups-of-sl4z-are-not-reduced-mf-proof
kind: route
title: Lift an MF embedding to an asymptotic homomorphism, correct it to genuine representations, and meet the fixed vector
target: matricially-stable-overgroups-of-sl4z-are-not-reduced-mf
requires: [sl4z-representations-have-sl2-invariant-vectors]
---

Suppose `iota : C*_r(Gamma) -> Q = prod_n M_(k_n) / sum_n M_(k_n)` is an
injective *-homomorphism.

1. **Lift.**  For `g in Gamma`, `iota(lambda(g))` is a unitary of `Q`.  Lift it
   to a contraction `(x_n) in prod_n M_(k_n)`; then `x_n^* x_n -> 1` in norm,
   so the unitary parts `phi_n(g)` of the polar decompositions satisfy
   `[(phi_n(g))] = iota(lambda(g))`.  Since `iota o lambda` is a homomorphism,
   `||phi_n(gh) - phi_n(g) phi_n(h)|| -> 0` for all `g, h`.
2. **Correct.**  Matricial stability gives homomorphisms `pi_n` with
   `||pi_n(g) - phi_n(g)|| -> 0`, so `[(pi_n(z))] = iota(lambda(z))` for every
   `z in C[Gamma]`.  The corona norm is `limsup_n` of the coordinate norms and
   `iota` is isometric, hence
   `limsup_n ||pi_n(z)|| = ||lambda_Gamma(z)||`.
3. **Fixed vector.**  Take `z = S + S^(-1) + T + T^(-1)` in the block `SL_2(Z)`
   of `SL_4(Z) <= Gamma`.  Each `pi_n|_(SL_4(Z))` is a finite-dimensional
   unitary representation, so by `sl4z-representations-have-sl2-invariant-vectors`
   it has a nonzero `SL_2(Z)`-fixed vector and `||pi_n(z)|| = 4` whenever
   `k_n >= 1`.  But `lambda_Gamma|_(SL_2(Z))` is a multiple of
   `lambda_(SL_2(Z))`, and `SL_2(Z)` is nonamenable, so
   `||lambda_Gamma(z)|| < 4` by Kesten.  Contradiction with step 2 (the
   `limsup` runs over the `n` with `k_n >= 1`, infinitely many because `iota`
   is injective on the infinite-dimensional algebra `C*_r(Gamma)`).

Step 3 needs the eigenvalue `4` in every coordinate, which is why genuine
matricial stability is required and the padded (weak) form does not suffice.
