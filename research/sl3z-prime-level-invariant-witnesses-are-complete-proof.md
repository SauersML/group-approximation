---
rg: 2
id: sl3z-prime-level-invariant-witnesses-are-complete-proof
kind: route
title: Jacquet module plus the column character stabilizer for non-cuspidals; Deligne-Lusztig count and Clifford transitivity for cuspidal constituents
target: sl3z-prime-level-invariant-witnesses-are-complete
requires: []
artifacts:
  - research/artifacts/sl3z-prime-level-witness-completeness-2026-09-13.md
---

The complete proof is in the artifact, section "Theorem E".

1. **Non-cuspidal.**  Transpose-inverse lets us assume
   `W = rho^(<e_12, e_13>) != 0`.  If `e_23` acts trivially on `W`, its normal
   closure `SL_2(F_p)` in coordinates `2,3` (a conjugate of `B_2`) fixes `W`.
   Otherwise take `v in W` on which `e_23` acts by a nontrivial `psi`.  Then `v`
   is an eigenvector of `<e_13, e_23>` whose character has stabilizer
   `N = {e_12(b)}` in `B_2`, and `N` fixes `v`.  Translates by distinct cosets of
   `N` are orthogonal, so their sum is a nonzero `B_2`-invariant vector.
2. **Cuspidal.**  `chi_pi` vanishes at elements whose semisimple part has an
   eigenvalue in `F_p` and is non-central.  Its values at unipotent types
   `(1,1,1)`, `(2,1)`, `(3)` are `(p-1)(p^2-1)`, `1-p`, `1`.  Every nonidentity
   element of `Omega` is regular unipotent or semisimple with eigenvalue 1.  So
   `dim pi^(Omega) = [(p-1)(p^2-1) + (p^2-1)] / (p(p^2-1)/2) = 2`.  Since `pi` is
   `GL_3`-stable, the same holds for every `Omega^(t)`.
3. **Split restriction.**  `GL_3(F_p)/(Z SL_3(F_p)) = F_p^x/(F_p^x)^3` permutes
   the three constituents simply transitively.  This gives
   `dim rho_j^(Omega^(t)) = dim rho_(sigma_t j)^(Omega)`, and summing over the
   classes gives `dim pi^(Omega) = 2`.

Check.  The exact census at `p = 7` (`experiments/sl3z-purely-matricial/dist3.c`,
two moduli) agrees with the claim.

- The block and `Omega^(1)` together miss four irreducibles, of degree `96`.
- Each `Omega^(t)` alone misses six: four of degree `96` and two of degree `57`.
- The block and all three `Omega^(t)` together miss none: all `64` irreducibles
  occur.
