---
rg: 2
id: sl3z-prime-level-sc-forces-congruence-sc-for-sl2z-proof
kind: route
title: Cuspidal restrictions to the block SL_2 are Reg minus Ind_U 1, and a square non-cube twist spreads every multiplicity evenly over cubic constituents
target: sl3z-prime-level-sc-forces-congruence-sc-for-sl2z
requires: [sl3z-prime-level-invariant-witnesses-are-complete]
artifacts:
  - research/artifacts/sl3z-prime-level-witness-completeness-2026-09-13.md
---

Artifact, section "Corollary G".

1. The block witness plus part 1 of
   `sl3z-prime-level-invariant-witnesses-are-complete` makes `rho_i` a cuspidal
   constituent for large `i`: a non-cuspidal representation has block-fixed
   vectors, and `||lambda(L_(B_2)/4)|| < 1`.
2. For cuspidal `pi`, the Deligne--Lusztig values give
   `pi|_(B_2) = Reg - Ind_U 1`.  So every nontrivial `sigma` in `Irr(SL_2(F_p))`
   occurs with multiplicity `dim sigma - dim sigma^U > 0`.
3. Cubic-twist constituents are permuted transitively by `Ad(diag(g^2,1,1))`.
   This element acts on `B_2` by a square diagonal automorphism, which fixes
   every `sigma`, so each constituent carries a third of each multiplicity.
4. The norm of a representation is the maximum over its constituents, so
   `||rho_i(z)|| = ||l^2_0(SL_2(F_(p_i)))(z)||` on `C[B_2(Z)]`.  The regular norm
   restricts: `||lambda_(SL_3(Z))(z)|| = ||lambda_(SL_2(Z))(z)||`.
5. Kesten gives `2 sqrt 3` for the Sanov subgroup, which is free of index 12.
