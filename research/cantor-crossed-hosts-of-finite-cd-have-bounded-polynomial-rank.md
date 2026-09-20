---
rg: 2
id: cantor-crossed-hosts-of-finite-cd-have-bounded-polynomial-rank
kind: claim
title: Cantor crossed products LC(X,k) ⋊ P have Hochschild dimension at most cd_k(P)+1, so B_Ω ⊗ L_∂ contains no polynomial ring in six variables
distinct_from:
  z2-sft-boundary-hosts-need-unboundedly-hard-sft-languages: that is a complexity obstruction, beating each recursive time bound with some decidable group; this is a homological obstruction, uniform in Ω and d, beating every Ω at once with the single group Z^6.
  cantor-crossed-hosts-are-closed-under-boundary-products: that says boundary products stay in the host class; this bounds the Hochschild dimension of every host of the class whose acting group has finite cohomological dimension.
  leavitt-tensor-global-dimension-bound: that bounds global dimension of B ⊗ L^(⊗d); this bounds Hochschild dimension of crossed products and turns it into a polynomial-rank bound.
invalidates:
  - cantor-crossed-hosts-via-boundary-products-of-z2-sft-hosts
---

**ESTABLISHED.** Let `k` be a field.
1. **Cantor coefficients.** If `X` is compact metrizable and totally disconnected,
   then `hd_k(LC(X, k)) <= 1`.
2. **Crossed products.** Let a group `P` act on a `k`-algebra `A` by automorphisms.
   Suppose the trivial module `k` has a projective `kP`-resolution of length `c`,
   i.e. `cd_k(P) <= c`. Then `hd_k(A ⋊ P) <= hd_k(A) + c`.
3. **Tensor products.** `hd_k(A ⊗_k C) <= hd_k(A) + hd_k(C)`.
4. **The boundary-product hosts.** For every free minimal `Z^2`-SFT `Ω` and every
   `d >= 2`:
   - `hd(B_Ω) <= 3`, where `B_Ω = LC(Ω, F_2) ⋊ Z^2`;
   - `hd(L_∂) <= 2`, where `L_∂ = LC(∂F_d, F_2) ⋊ F_d`;
   - so `hd(B_Ω ⊗ L_∂) <= 5`, and by `polynomial-rank-is-at-most-hochschild-dimension`
     the host has polynomial rank at most `5`.
5. **Class kill.** Every host `LC(X, k) ⋊ P` with `cd_k(P) = c < ∞` has polynomial
   rank at most `c + 1`. So it contains no copy of `k[Z^(c+2)]`. For example, no such
   host contains `k[Z wr Z]`, which contains `k[Z^m]` for all `m`.

**Consequence.** `F_2[Z^6]` contains `F_2[x_1..x_6]`, embedded unitally or not. It has
no embedding into any `B_Ω ⊗ L_∂`. `Z^6` is finitely generated with solvable word
problem. So `decidable-algebras-embed-in-z2-sft-boundary-product-hosts` is false, and
its route `cantor-crossed-hosts-via-boundary-products-of-z2-sft-hosts` is dead.

For `decidable-group-algebras-have-fp-cantor-crossed-hosts`, part 5 says a positive
answer needs, for inputs such as `Z wr Z`, an acting group `P` of infinite
cohomological dimension over `F_2`.

**Proof.** Route `cantor-crossed-hochschild-bound-via-fox-and-idempotent-telescope`,
which is self-contained apart from the ESTABLISHED
`polynomial-rank-is-at-most-hochschild-dimension`.
