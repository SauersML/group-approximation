---
rg: 2
id: subshift-el-2-simple-modulo-centre-every-finite-field-proof
kind: route
title: Short-tower commutator with e_V and e_V u roots, a non-scalar SL_d(F_q) extraction, and Peirce-block level propagation
target: subshift-el-2-simple-modulo-centre-every-finite-field
requires:
  - complementary-full-idempotents-make-el-2-kazhdan
  - minimal-subshift-algebra-is-simple-lef-ring
artifacts:
  - research/artifacts/sk-el2-fq-all-fields-2026-09-13.md
---

Full derivation: `research/artifacts/sk-el2-fq-all-fields-2026-09-13.md` §2–§4.

**Centre (Lemma C).** If g ∈ GL_2(R) commutes with e_12(1), e_21(1), e_12(u) and every e_12(e_U), then g = λI_2,
λ ∈ F_q^×. The first two force g = cI_2. Commuting with e_U kills the u^j-coefficients of c for j ≠ 0, because T has no
periodic points. Commuting with u makes c invariant, hence constant by minimality.

**Simplicity.** Let g ∈ N ⊴ G be noncentral, w its propagation bound, and m = w+1. Call V small if V ∩ T^jV = ∅ for
0 < |j| ≤ 2m, and every coefficient f of g^{±1} has f∘T^i constant on V for |i| ≤ m.
1. Some h = e_ij(s), s ∈ {e_V, e_V u}, V small, does not commute with g. Otherwise additivity over small partitions and
   Lemma C make g scalar.
2. With ε_ab = e_(T^aV)u^(a−b), |a|,|b| ≤ m, the map ψ(E_((p,a),(p',b))) = ε_ab E_pp' embeds M_d(F_q), d = 2(2m+1).
   - Transvections between different blocks are roots. Those inside a block are commutators through the other block.
     So the copy S of SL_d(F_q) lies in G.
   - The product formula (f u^i)(e_V u^c)(f'u^j) ∈ F_q ε_(i,−(c+j)) puts k−I and k^{-1}−I into ψ(M_d(F_q)), with
     second tower index in [−m, w]. So k = image of κ ∈ GL_d(F_q).
   - κ fixes the basis vectors at level +m, so κ is not scalar.
3. [k,S] ⊆ N ∩ S ⊴ S. If N ∩ S were central, σ ↦ [k,σ] would be a homomorphism from the perfect group S to Z(S), so κ
   would centralize SL_d(F_q) and be scalar. So N ∩ S = S, since SL_d(F_q), d ≥ 6, is quasisimple. So e_12(e_V) ∈ N.
4. e_V and 1−e_V are full (translates cover X; V ≠ X). In the Peirce blocks E_1 = e_VE_11, E_2 = e_VE_22,
   E_3 = (1−e_V)I_2:
   - J_AB = {x ∈ E_AME_B : I+x ∈ N} satisfies J_AB·E_BME_C ⊆ J_AC and E_CME_A·J_AB ⊆ J_CB, by
     [I+x, I+y] = I+xy when yx = 0.
   - Starting from e_VE_12 ∈ J_12, the chain J_13, J_12, J_32, J_31, J_23, J_21 fills every block.
   - The Y_AB = I+E_AME_B lie in G and generate it (sk-el2 part 1, Lemma 2(i)(ii), characteristic-free). So N = G.

**Remaining properties.**
- Infinite: e_12(LC(X,F_q)) ⊆ G and Z(G) is finite.
- (T): `complementary-full-idempotents-make-el-2-kazhdan` with e = e_W, ∅ ≠ W ≠ X. Finite generation from (T)
  (Bekka–de la Harpe–Valette Thm 1.3.1, recalled).
- LEF: the unital embedding R → ∏_ω M_(N_k)(F_q) (`minimal-subshift-algebra-is-simple-lef-ring` item 3) sends scalars
  to scalars. For finitely many g g'^{-1} ∉ Z(G), the nonzero matrices g g'^{-1} − λI_2 stay nonzero for ω-almost
  every k. So G/Z(G) has injective product-preserving partial models into PGL_(2N_k)(F_q).
