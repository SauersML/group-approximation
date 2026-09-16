---
rg: 2
id: mod3-twisted-fibre-llp-forces-f2xf2-llp-proof
kind: route
title: Corner identification, induced-representation expectation and untwisting put C*(K) inside the twisted fibre with a ucp left inverse
target: mod3-twisted-fibre-llp-forces-f2xf2-llp
requires:
  - deligne-multiplier-trivial-on-sl2xsl2-and-parabolics
artifacts:
  - research/artifacts/sp4-mod3-twisted-fibre-f2xf2-calibration-2026-09-16.md
---

Full proofs are in the artifact, sections 7 and 8.  Section 3 has the Sanov
lemma.  No LLP permanence theorem from the literature is imported.  The
subgroup-algebra permanence needed is proved directly.

Notation: `E_3 -> Sp_4(Z)` with central kernel `<z>` of order three.
`chi_1, chi_2` are the faithful characters of `<z>`, and
`p_chi = (1/3) sum_k chi(z)^{-k} u_z^k`, a central projection of `C^*(E_3)`.
Put `A_chi = p_chi C^*(E_3)`.

1. **Twisted fibres are corners (Lemma 7.1).**
   - Choose a section `sigma` with `sigma(1) = 1`, and write
     `sigma(g) sigma(h) = c(g,h) sigma(gh)`.
   - `v_g -> p_chi u_{sigma(g)}` defines
     `C^*(Sp_4(Z); chi o c) -> A_chi`.  It is an isomorphism.  The inverse is
     induced by the representation `sigma(g) z^k -> chi(z)^k v_g` of `E_3`,
     which sends `p_chi` to `1`.
   - `chi_1 o c = alpha` and `chi_2 o c = alpha^2`.
2. **Expectation onto a subgroup algebra (Lemma 7.2).**
   - Let `K~ = p^{-1}(K) <= E_3`.  Induce a faithful representation of
     `C^*(K~)` up to `E_3`, and compress to the coset `K~`.  This gives a ucp
     map `Phi` with `Phi(u_g) = 1_{K~}(g) u_g`.
   - `Phi` is a left inverse of the inclusion `iota`, and it is
     `C^*(K~)`-bimodular.
   - Because `z in K~` is central, `iota(p_chi) = p_chi` and
     `Phi(p_chi x) = p_chi Phi(x)`.  So both maps restrict to the corners, and
     `iota o Phi` is a conditional expectation.
3. **Untwisting (Lemma 7.3).**
   - The required claim gives `phi : p^{-1}(H) -> T` with `phi(z) = omega`.
     Restrict it to `K~`.
   - For `chi_1` use `phi`, and for `chi_2` use `phi^2`.  The result is
     `phi_chi` with `phi_chi(z) = chi(z)`.
   - Then `u_{q(x)} -> phi_chi(x)^{-1} p_chi u_x` defines an isomorphism
     `C^*(K) -> p_chi C^*(K~)`.  The inverse is induced by
     `x -> phi_chi(x) u_{q(x)}`.
4. **LLP descends along ucp left inverses (Lemma 7.4).**
   - Let `j : C -> A` be an injective unital *-homomorphism, and `E` a ucp
     map with `E o j = id`.
   - Given a ucp `T : C -> B/I` and a finite-dimensional operator system
     `F <= C`, lift `T o E` on `j(F)`, and precompose with `j`.
5. **Assembly (section 8).**
   - `j = iota_chi o Theta` and `E = Theta^{-1} o Phi_chi`.
   - `j` is injective unital, `E` is ucp, and `E o j = id`.  `j o E` is the
     conditional expectation of step 2.
6. **Instances.**
   - `M_1 = [[1,2],[0,1]]` and `M_2 = [[1,0],[2,1]]` generate a free group of
     rank two.  The proof is ping-pong on `{|x| > |y|}` and `{|x| < |y|}`
     (Lemma 3.3).  Placing it in both blocks gives `F_2 x F_2 <= S`.
   - The splitting part of the required claim, over `F x F'`, supplies `phi`.
   - `E = N(Z) x| S_2(Z)` is an index-two subgroup of `P_K(Z)`, so it is
     covered as well (artifact, remark 9.5).

The only definitional input is the local ucp-lifting form of Kirchberg's LLP
stated in Lemma 7.4.  The bibliographic location of that definition was not
re-verified in this session.
