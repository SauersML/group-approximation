---
rg: 2
id: sofic-implies-linear-sofic-over-every-field-proof
kind: route
title: Permutation matrices have rank distance comparable to Hamming distance over every field
target: sofic-implies-linear-sofic-over-every-field
requires: []
---

Let `p in S_n` with permutation matrix `A_p e_i = e_(p(i))` over `F`.

1. `A_p v = v` exactly when `v` is constant on every cycle of `p`, so
   `dim ker(A_p - I) = cyc(p)` over every field, and

   ```text
   rho(I - A_p) = 1 - cyc(p)/n.
   ```

2. `fix(p) <= cyc(p) <= fix(p) + (n - fix(p))/2`, because a non-fixed cycle
   has length at least two.  With `d_H(p,1) = 1 - fix(p)/n` this gives

   ```text
   rho(I - A_p) <= d_H(p,1) <= 2 rho(I - A_p).
   ```

3. `p -> A_p` is an exact homomorphism and both metrics are bi-invariant, so
   `rho(A_p - A_q) = rho(I - A_(p^-1 q))` and likewise for `d_H`.

Let `Phi: G -> prod_omega (S_(n_k), d_H)` be an injective sofic morphism with
lifts `phi_k`.  Put `Theta = prod_omega A_(phi_k(g))`.  By step 2 the left
inequality makes `Theta` well defined and a homomorphism on the quotient by
`{rho_omega(a - I) = 0}`; the right inequality makes it injective.  End proof.

Source: Arzhantseva--Paunescu, arXiv:1212.6780, Proposition 4.5, where the
same computation is written over `C` (citing Lupini for step 1).  Nothing in
it uses the characteristic.
