---
rg: 2
id: sl3z-dense-with-unipotent-lattice-has-finite-index-proof
kind: route
title: Three planes in general position turn a unipotent lattice into all six elementary directions
target: sl3z-dense-with-unipotent-lattice-has-finite-index
requires:
  - sl3z-congruence-elementary-generators-have-finite-index
---

**Notation.** For a rational plane `W`, let `mu_W` be a nonzero functional
with kernel `W`. The unipotent radical of `Stab(W)` is
`U_W = {I + w mu_W^T : w in W}`, which is additive in `w` because
`mu_W(w) = 0`. `U_W(Z)` is a rank-two lattice in `U_W(R)`. Root subgroups are
`R(l, mu) = {I + t l mu^T}` with `mu(l) = 0`.

**The line case reduces to the plane case.** The automorphism
`theta(g) = (g^T)^-1` of `SL_3(Z)` preserves Zariski density and carries
unipotent radicals of line stabilizers to those of plane stabilizers. So
assume `N` contains a finite-index subgroup of `U_W(Z)` for a rational plane
`W`.

1. **Conjugates.** For `gamma in N`, `N` contains a rank-two lattice of
   `U_{gamma W}(R)`.
2. **General position.** The pairs `(g_2, g_3)` for which `W`, `g_2 W`,
   `g_3 W` are pairwise distinct with zero triple intersection form a nonempty
   Zariski-open subset of `SL_3 x SL_3`. `N x N` is Zariski dense there. So
   there are `gamma_2, gamma_3 in N` with `W_1 = W`, `W_2 = gamma_2 W`,
   `W_3 = gamma_3 W` in general position.
3. **Basis.** Let `e_1` span `W_2 ∩ W_3`, `e_2` span `W_1 ∩ W_3`, and `e_3`
   span `W_1 ∩ W_2`. These are rational lines.
   - `e_2` and `e_3` are independent, otherwise they would lie in
     `W_1 ∩ W_2 ∩ W_3 = 0`. So they span `W_1`, and similarly for `W_2` and
     `W_3`.
   - So `e_1, e_2, e_3` is a basis (else `W_1 = W_2`).
   - The dual basis satisfies `ker e_j^* = W_j`, so `e_j^*` is proportional
     to `mu_{W_j}`.
4. **All six root directions.** For `i != j`, `e_i in W_j`, so
   `R(e_i, e_j^*) <= U_{W_j}`. `N ∩ U_{W_j}` contains a rank-two lattice, and
   `R(e_i, e_j^*)` is a rational line in `U_{W_j}`. So `N` contains
   `I + c_ij e_i (e_j^*)^T` for some `c_ij in Q^×`.
5. **Integral generators.** Let `g in GL_3(Q)` send the standard basis to
   `(e_1, e_2, e_3)`. Then `g^-1 N g` contains `e_ij(c_ij)`. Write
   `c_ij = a_ij / b_ij` in lowest terms. Then `e_ij(a_ij) = e_ij(c_ij)^{b_ij}`
   lies in `g^-1 N g`, and so does `e_ij(m)` for `m = lcm |a_ij|`. So
   `g^-1 N g >= E(m)`.
6. **Finite index.** By `sl3z-congruence-elementary-generators-have-finite-index`,
   `E(m)` is a lattice in `SL_3(R)`. So `N` contains the lattice
   `g E(m) g^-1`. A subgroup of the lattice `SL_3(Z)` that contains a lattice
   has finite index, by comparing covolumes.
