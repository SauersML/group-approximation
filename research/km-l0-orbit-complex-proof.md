---
rg: 2
id: km-l0-orbit-complex-proof
kind: route
title: Equivariant spectral sequence collapse over finite stabilizers
target: km-l0-cohomology-is-the-49-orbit-invariants-complex
requires:
  - km-thick-part-two-connected-and-lattice-is-f3
  - simple-kazhdan-kac-moody-lattices-exist
---

Three ingredients, each already in hand or classical.

1. **Comparison in low degrees.**  `X^` is 2-connected and cocompact
   (`km-thick-part-two-connected-and-lattice-is-f3`), so in the
   double-complex spectral sequence with `E_2^(p,q) =
   H^p(Lambda; H^q(X^) tensor-coeff V)` the rows `q = 1, 2` vanish
   and `H^n_Lambda(X^; V) = H^n(Lambda; V)` for `n <= 2` (Brown VII.7
   style comparison; the same argument already used for the group-ring
   computation).

2. **Stabilizer collapse.**  The action is type-preserving on each
   factor, hence fixes every product cell pointwise (no orientation
   twist), and every cell stabilizer is a FINITE Birkhoff intersection
   `P_J^+ cap P_K^- = T . <U_alpha : alpha in Phi_J^- cup Phi_K^+>`
   (finiteness: properness of the diagonal action; the root content
   is exactly `Phi_J^- cup Phi_K^+` since `U_gamma <= P_J^+` iff
   `gamma in Phi^+ cup Phi_J^-` and `U_gamma <= P_K^-` iff `gamma in
   Phi^- cup Phi_K^+`, and the refined Birkhoff decomposition of the
   RGD system (Abramenko--Remy) gives the Levi form `L_(J cap K) .
   (unipotent of order q^(N_J + N_K - 2 N_(J cap K)))`;
   `Lambda`-transitivity on opposite chamber pairs is the `w = 1`
   Birkhoff cell).  For a finite group `F` and uniquely
   divisible `V`, `H^q(F; V)` is killed by `|F|` and divisible, so it
   vanishes for `q > 0`.  Hence the isotropy spectral sequence
   `E_1^(p,q) = product over p-orbits of H^q(Stab; V) =>
   H^(p+q)_Lambda(X^; V)` is concentrated in `q = 0` and degenerates
   to the cochain complex of orbit invariants.

3. **Orbit bookkeeping.**  A pair of simplices of cotypes `(J,K)` lies
   in `X^ = Z_(<=0)` iff some containing chamber pair is opposite, iff
   `1 in W_J w W_K`, iff the `(J,K)`-reduced representative is `1`:
   one orbit per pair of proper subsets `J, K` of `S`, `7 x 7 = 49`
   in all, of dimension `4 - |J| - |K|`, giving `9, 18, 15, 6, 1` in
   dimensions `0..4`.  (This corrects the earlier headline count of
   58 recorded in the LP node's attempt list; the per-dimension
   breakdown there was already `1 + 6 + 15 + 18 + 9 = 49`.)
