---
rg: 2
id: rational-character-approximation-determinant-proof
kind: route
title: Rational representations of finite groups preserve lattices, so models of integral matrices are integer matrices with real spectrum whose moments converge
target: rational-character-approximable-groups-obey-determinant
requires:
  - integer-root-limits-are-galois-balanced-serre-measures
  - determinant-conjecture-iff-serre-class-spectra
artifacts:
  - research/artifacts/determinant-integer-root-limits-2026-09-12.md
---

Let `A = sum_g a_g g in M_n(Z[G])` be self-adjoint, with `a_(g^-1) = a_g^T`.
Fix `j`, and let `S` contain every product of at most `j` elements of
`supp A cup {e}`.

1. **Integral form.** `L = sum_(f in F) rho(f) Z^d` is an `F`-stable lattice. In
   a basis of `L`, `rho(F) <= GL_d(Z)`. So
   `A_phi = sum_g a_g (x) rho phi(g)` is an integer `nd x nd` matrix, and its
   characteristic polynomial is monic integral.
2. **Real spectrum.** `rho phi(g^-1) = rho phi(g)^-1` is the `q`-adjoint of
   `rho phi(g)`, so `A_phi` is self-adjoint for the positive form `I_n (x) q`.
   Its spectrum is real, of norm at most `sum_g ||a_g||_1`.
3. **Moments.** For `g_1..g_k` in `supp A`, `k <= j`, telescoping with
   `q`-unitaries gives
   `||rho phi(g_1)...rho phi(g_k) - rho phi(g_1...g_k)||_2 <= (k-1) eps`. So
   `(1/d) Tr rho phi(g_1)...rho phi(g_k)` is within `O(k eps)` of
   `delta_(g_1...g_k = e)`. Expanding
   `(1/nd) Tr (A_phi)^k` and `(1/n) (Tr (x) tau)(A^k)` as the same finite sums,
   they differ by `O(eps)`.
4. **Limit.** Along `eps -> 0` and `j -> infinity`, moments converge with
   uniformly bounded support, so the eigenvalue distributions of `A_phi`
   converge weakly to `mu_A`. So `mu_A` is an integer root limit.
5. **Conclusion.** `integer-root-limits-are-galois-balanced-serre-measures` puts
   `mu_A` in the Serre class with Galois-balanced integral atoms.
   `determinant-conjecture-iff-serre-class-spectra` gives the determinant
   conjecture, and the atoms of `mu_A` are the eigenvalues of `A` with masses
   `dim ker / n`. QED
