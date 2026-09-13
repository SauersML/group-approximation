---
rg: 2
id: reduced-group-algebras-contain-no-nonzero-ghosts-proof
kind: route
title: Matrix entries of reduced group algebra elements are constant along right translates
target: reduced-group-algebras-contain-no-nonzero-ghosts
requires: []
---

1. **Right translations commute with `T`.** Put `rho_h delta_k = delta_(k h^-1)`.
   - Each `rho_h` is unitary and commutes with every `lambda_s`, since
     `rho_h lambda_s delta_k = delta_(s k h^-1) = lambda_s rho_h delta_k`.
   - So `1_n ⊗ rho_h` commutes with `M_n(lambda(C[G]))`, and hence with its
     norm closure `M_n(C*_r G)`.
2. **The entries depend only on `g h^-1`.** Note `delta_h = rho_(h^-1) delta_e`
   and `rho_(h^-1)^* = rho_h`. Then

   ```text
   < T (e_i ⊗ delta_h), e_j ⊗ delta_g >
     = < rho_(h^-1) T (e_i ⊗ delta_e), e_j ⊗ delta_g >
     = < T (e_i ⊗ delta_e), e_j ⊗ delta_(g h^-1) >
     =: c_ij(g h^-1).
   ```

3. **A ghost has `c_ij = 0`.** Fix `k ∈ G` and `eps > 0`, and let `F` be as in
   the ghost condition.
   - `G` is infinite, so there is `h ∉ F`, and then `(kh, h) ∉ F × F`.
   - So `|c_ij(k)| = |< T (e_i ⊗ delta_h), e_j ⊗ delta_(kh) >| < eps`.
   - As `eps` was arbitrary, `c_ij(k) = 0` for all `i, j, k`.
4. **`T = 0`.**
   - By step 3, `T (e_i ⊗ delta_e) = 0` for every `i`.
   - Then `T (e_i ⊗ delta_h) = rho_(h^-1) T (e_i ⊗ delta_e) = 0` for every `h`.
   - These vectors span a dense subspace, so `T = 0`.

**Corollary.** A compact operator is a ghost. So `K(C^n ⊗ l^2 G) ∩ M_n(C*_r G) = 0`
for infinite `G`.
