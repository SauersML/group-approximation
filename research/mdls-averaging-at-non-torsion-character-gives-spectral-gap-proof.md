---
rg: 2
id: mdls-averaging-at-non-torsion-character-gives-spectral-gap-proof
kind: route
title: Non-torsion characters have unipotent stabilizers, so the orbit span is induced from an amenable subgroup
target: mdls-averaging-at-non-torsion-character-gives-spectral-gap
requires: []
artifacts:
  - research/artifacts/sl4z-mf-corona-reduction-2026-09-13.md
---

Notation: `G = SL_2(Z)` acts on characters by `(g.theta)(a) = theta(g^-1 a)`, that is
`theta -> theta g^-1` on row vectors mod `Z^2`.  For `a in A` and `v in H_theta`,
`sigma(a) sigma(g) v = sigma(g) sigma(g^-1 a g) v = theta(g^-1 a) sigma(g) v`.  So
`sigma(g) H_theta = H_(g.theta)`.

1. **The stabilizer is amenable.**
   - Let `g in Stab_G(theta)`.  Then `theta (g^-1 - I) in Z^2`.
   - If `g^-1 - I` were invertible over `Q`, then `theta` would lie in
     `Z^2 (g^-1 - I)^-1 subset Q^2`, a torsion point.  So `det(g - I) = 0`: `g` has
     eigenvalue `1`, hence trace `2`, hence `g` is unipotent.
   - So `Stab_G(theta)` consists of unipotent elements.  By Kolchin it is conjugate into
     the upper unitriangular matrices, so it is trivial or infinite cyclic.  Either way it
     is amenable.
2. **The orbit span is induced.**
   - The subspaces `H_(g.theta)`, for `g` in `G / Stab_G(theta)`, carry distinct
     characters of `A`, so they are pairwise orthogonal.  `G` permutes them transitively.
   - `H_theta` is invariant under `L = Stab_G(theta)`.  Let `tau = sigma|_(H_theta)`
     restricted to `L`.
   - Then `K` is the orthogonal sum of the `sigma(g) H_theta`, and `sigma|_K`, restricted
     to `G`, is unitarily equivalent to `Ind_L^G tau`.  For discrete groups this is the
     standard characterization of induced representations by a transitive system of
     imprimitivity.
3. **Weak containment.**  (Standard, not re-read: Bekka--de la Harpe--Valette, *Kazhdan's
   Property (T)*, Appendix F.)
   - `L` is amenable, so `lambda_L` weakly contains `1_L`.
   - By Fell absorption, `tau = tau (x) 1_L` is weakly contained in `tau (x) lambda_L`,
     which is a multiple of `lambda_L`.
   - Induction preserves weak containment, and `Ind_L^G lambda_L = lambda_G`.  So
     `Ind_L^G tau` is weakly contained in `lambda_G`.
4. **The norm bound.**  Weak containment bounds the norm of every group-algebra element:
   `||sigma|_K(z)|| <= ||lambda_G(z)||`.  `G = SL_2(Z)` is nonamenable and
   `{S^(+-1), T^(+-1)}` generates it, so Kesten's criterion gives `||lambda_G(z)|| < 4`.
