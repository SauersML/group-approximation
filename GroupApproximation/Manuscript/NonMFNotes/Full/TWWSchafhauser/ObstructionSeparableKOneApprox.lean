import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSeparableKDist
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.KTheoryNonUnital
import GroupApproximation.Analysis.PolarLiftingGeneralCStar

/-!
# Separable inheritance, step 1: `K₁` along an increasing chain

Lane `TWWSch3d2S`, work order `WO-TWWSch-3d2-S`.
Manuscript: `non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378). That
theorem cites Tikuisis--White--Winter, Ann. of Math. 185 (2017), Theorem A, through
C. Schafhauser, J. reine angew. Math. 759 (2020), Lemma 4.4. The separable reduction there
(B. Blackadar, *Operator Algebras*, II.8.5) needs `K₁(D ∩ J) = 0` along an increasing chain of
separable subalgebras `D`. This file proves the continuity half of that statement
(M. Rørdam, F. Larsen, N. Laustsen, *An introduction to K-theory for C⋆-algebras*, 2.1.8 and
8.1): for `D_∞ = closure (⋃ₖ Dₖ)`, every class in `K₁(D_∞ ∩ J)` comes from some `K₁(Dₖ ∩ J)`.

* `cStarMat_norm_le_sum_norm`: `‖M‖ ≤ ∑ⱼ ∑ᵢ ‖Mᵢⱼ‖`;
* `norm_matMapHom_of_injective`: an injective unital ⋆-homomorphism is isometric on matrices;
* `unitaryClass_mk_eq_of_norm_sub_lt_two`: unitaries at distance `< 2` have the same class
  (RLL 2.1.3);
* `exists_unitary_matMap_near`: a matrix `y` with `‖v - φ(y)‖ ≤ 1/10` for a unitary `v` has a
  unitary polar part `w` with `[φ(w)] = [v]` (RLL 2.1.8 for the polar decomposition);
* `sepIncl J h`: the inclusion `D ∩ J → D' ∩ J` for `D ≤ D'`;
* `exists_kOneN_map_eq_of_chain`: every class of `K₁(D_∞ ∩ J)` is the image of a class of
  `K₁(Dₖ ∩ J)` for some `k`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

noncomputable section

/-! ### Matrix norms and unitary classes -/

section Matrix

variable {A A' : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra A'] [PartialOrder A'] [StarOrderedRing A']

open CStarModule WithCStarModule in
/-- The C⋆-norm of a matrix is at most the sum of the norms of its entries. -/
theorem cStarMat_norm_le_sum_norm {n : ℕ} (M : CStarMat n A) :
    ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
  rw [CStarMatrix.norm_def]
  refine (CStarMatrix.toCLM M).opNorm_le_bound (by positivity) fun v ↦ ?_
  simp only [CStarMatrix.toCLM_apply_eq_sum, Finset.sum_mul]
  apply pi_norm_le_sum_norm _ |>.trans
  gcongr with i _
  apply norm_sum_le _ _ |>.trans
  gcongr with j _
  apply norm_mul_le _ _ |>.trans
  rw [mul_comm]
  gcongr
  exact norm_apply_le_norm v j

/-- A unitary of a C⋆-algebra has norm at most one. -/
theorem norm_unitary_coe_le_one {E : Type*} [CStarAlgebra E] (u : unitary E) :
    ‖(u : E)‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [Subsingleton.elim (u : E) 0, norm_zero]
    exact zero_le_one
  · exact le_of_eq (CStarRing.norm_coe_unitary u)

/-- Entrywise application of `ψ`, as a non-unital ⋆-homomorphism of matrix algebras. -/
theorem matMapHom_eq_mapₙₐ (ψ : A' →⋆ₐ[ℂ] A) (n : ℕ) (M : CStarMat n A') :
    CStarMatrix.mapₙₐ (n := Fin n) (ψ : A' →⋆ₙₐ[ℂ] A) M = matMapHom ψ n M :=
  CStarMatrix.ext fun _ _ => rfl

/-- **Injective ⋆-homomorphisms are isometric on matrices**: `M_n(ψ)` is an injective
⋆-homomorphism of C⋆-algebras. -/
theorem norm_matMapHom_of_injective (ψ : A' →⋆ₐ[ℂ] A) (hψ : Function.Injective ψ) (n : ℕ)
    (M : CStarMat n A') : ‖matMapHom ψ n M‖ = ‖M‖ := by
  have hinj : Function.Injective (CStarMatrix.mapₙₐ (n := Fin n) (ψ : A' →⋆ₙₐ[ℂ] A)) := by
    intro M N h
    refine CStarMatrix.ext fun i j => hψ ?_
    have h' := congrArg (fun P : CStarMat n A => P i j) h
    rw [matMapHom_eq_mapₙₐ, matMapHom_eq_mapₙₐ] at h'
    exact h'
  have h := NonUnitalStarAlgHom.norm_map _ hinj M
  rw [matMapHom_eq_mapₙₐ] at h
  exact h

/-- **Unitaries at distance `< 2` are homotopic** (RLL 2.1.3): `u⁻¹v` lies within `2` of `1`. -/
theorem unitaryClass_mk_eq_of_norm_sub_lt_two {E : Type*} [CStarAlgebra E] {u v : unitary E}
    (h : ‖(v : E) - u‖ < 2) :
    (QuotientGroup.mk u : UnitaryClass E) = QuotientGroup.mk v := by
  rw [QuotientGroup.eq]
  apply mem_unitaryComponentOne_of_norm_sub_one_lt_two
  have hc : ((u⁻¹ * v : unitary E) : E) - 1 = star (u : E) * ((v : E) - u) := by
    show star (u : E) * (v : E) - 1 = star (u : E) * ((v : E) - u)
    rw [mul_sub, Unitary.star_mul_self_of_mem u.prop]
  have hn : ‖star (u : E) * ((v : E) - u)‖ = ‖(v : E) - u‖ :=
    CStarRing.norm_coe_unitary_mul (star u) _
  rw [hc, hn]
  exact h

/-- **Perturbation of approximate unitaries into a subalgebra** (RLL 2.1.8). Let `ψ` be an
injective unital ⋆-homomorphism, `v` a unitary over the target and `y` a matrix over the source
with `‖v - ψ(y)‖ ≤ 1/10`. Then `y` is almost unitary, its polar part `w` is a unitary, and
`ψ(w)` lies within `2` of `v`, so `[ψ(w)] = [v]`. -/
theorem exists_unitary_matMap_near (ψ : A' →⋆ₐ[ℂ] A) (hψ : Function.Injective ψ) {n : ℕ}
    (v : unitary (CStarMat n A)) (y : CStarMat n A')
    (hy : ‖(v : CStarMat n A) - matMapHom ψ n y‖ ≤ 1 / 10) :
    ∃ w : unitary (CStarMat n A'),
      (QuotientGroup.mk (matMapUnitary ψ n w) : UnitaryClass (CStarMat n A)) =
        QuotientGroup.mk v := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : CStarMat n A' →⋆ₙₐ[ℂ] CStarMat n A, ∀ M, Φ M = matMapHom ψ n M :=
    ⟨_, matMapHom_eq_mapₙₐ ψ n⟩
  have hΦ1 : Φ 1 = 1 := (hΦ 1).trans (map_one _)
  have hiso : ∀ M, ‖Φ M‖ = ‖M‖ := by
    intro M
    rw [hΦ]
    exact norm_matMapHom_of_injective ψ hψ n M
  obtain ⟨V, hVdef⟩ : ∃ V : CStarMat n A, V = v := ⟨_, rfl⟩
  have hVs : star V * V = 1 := by
    rw [hVdef]
    exact Unitary.star_mul_self_of_mem v.prop
  have hVs' : V * star V = 1 := by
    rw [hVdef]
    exact Unitary.mul_star_self_of_mem v.prop
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = ‖V - Φ y‖ := ⟨_, rfl⟩
  have he : e ≤ 1 / 10 := by
    rw [hedef, hΦ, hVdef]
    exact hy
  have he0 : 0 ≤ e := by
    rw [hedef]
    exact norm_nonneg _
  have hV : ‖V‖ ≤ 1 := by
    rw [hVdef]
    exact norm_unitary_coe_le_one v
  have hY : ‖Φ y‖ ≤ 1 + e := by
    have h1 : Φ y = V - (V - Φ y) := (sub_sub_cancel V (Φ y)).symm
    calc ‖Φ y‖ = ‖V - (V - Φ y)‖ := by rw [← h1]
      _ ≤ ‖V‖ + ‖V - Φ y‖ := norm_sub_le _ _
      _ ≤ 1 + e := by linarith
  have hYs : ‖star (Φ y) - star V‖ = e := by
    rw [← star_sub, norm_star, norm_sub_rev, hedef]
  have hYV : ‖Φ y - V‖ = e := by
    rw [norm_sub_rev, hedef]
  have hy1 : ‖y‖ ≤ 1 + e := by
    rw [← hiso y]
    exact hY
  -- the two Gram defects of `y`
  have hg1 : ‖star y * y - 1‖ ≤ (1 + e) * e + e := by
    have hmap : Φ (star y * y - 1) = star (Φ y) * Φ y - star V * V := by
      rw [map_sub, map_mul, map_star, hΦ1, hVs]
    have hsplit : star (Φ y) * Φ y - star V * V =
        star (Φ y) * (Φ y - V) + (star (Φ y) - star V) * V := by
      noncomm_ring
    rw [← hiso, hmap, hsplit]
    calc ‖star (Φ y) * (Φ y - V) + (star (Φ y) - star V) * V‖
        ≤ ‖star (Φ y)‖ * ‖Φ y - V‖ + ‖star (Φ y) - star V‖ * ‖V‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ = ‖Φ y‖ * e + e * ‖V‖ := by rw [norm_star, hYs, hYV]
      _ ≤ (1 + e) * e + e * 1 :=
          add_le_add (mul_le_mul_of_nonneg_right hY he0) (mul_le_mul_of_nonneg_left hV he0)
      _ = (1 + e) * e + e := by ring
  have hg2 : ‖y * star y - 1‖ ≤ (1 + e) * e + e := by
    have hmap : Φ (y * star y - 1) = Φ y * star (Φ y) - V * star V := by
      rw [map_sub, map_mul, map_star, hΦ1, hVs']
    have hsplit : Φ y * star (Φ y) - V * star V =
        (Φ y - V) * star (Φ y) + V * (star (Φ y) - star V) := by
      noncomm_ring
    rw [← hiso, hmap, hsplit]
    calc ‖(Φ y - V) * star (Φ y) + V * (star (Φ y) - star V)‖
        ≤ ‖Φ y - V‖ * ‖star (Φ y)‖ + ‖V‖ * ‖star (Φ y) - star V‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ = e * ‖Φ y‖ + ‖V‖ * e := by rw [norm_star, hYs, hYV]
      _ ≤ e * (1 + e) + 1 * e :=
          add_le_add (mul_le_mul_of_nonneg_left hY he0) (mul_le_mul_of_nonneg_right hV he0)
      _ = (1 + e) * e + e := by ring
  have hsmall : (1 + e) * e + e ≤ 21 / 100 := by
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr he)]
  have hg1' : ‖star y * y - 1‖ ≤ 1 / 2 := by linarith
  have hg2' : ‖y * star y - 1‖ ≤ 1 / 2 := by linarith
  have hw := PolarLiftingGeneralCStar.polarUnitary_mem_unitary hg1' hg2'
  have hwy := PolarLiftingGeneralCStar.norm_polarUnitary_sub_le hg1'
  refine ⟨⟨PolarLiftingGeneralCStar.polarUnitary y, hw⟩, ?_⟩
  apply unitaryClass_mk_eq_of_norm_sub_lt_two
  have hcoe : ((matMapUnitary ψ n ⟨PolarLiftingGeneralCStar.polarUnitary y, hw⟩ :
      unitary (CStarMat n A)) : CStarMat n A) = Φ (PolarLiftingGeneralCStar.polarUnitary y) :=
    (hΦ _).symm
  rw [hcoe, ← hVdef]
  have hprod : ‖y‖ * ‖star y * y - 1‖ ≤ 11 / 10 * (21 / 100) :=
    mul_le_mul (by linarith) (by linarith) (norm_nonneg _) (by norm_num)
  have hdiff : ‖Φ y - Φ (PolarLiftingGeneralCStar.polarUnitary y)‖ ≤ 1 / 2 := by
    rw [← map_sub, hiso, norm_sub_rev]
    linarith
  calc ‖V - Φ (PolarLiftingGeneralCStar.polarUnitary y)‖
      ≤ ‖V - Φ y‖ + ‖Φ y - Φ (PolarLiftingGeneralCStar.polarUnitary y)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < 2 := by linarith

end Matrix

/-! ### The chain of ideals `Dₖ ∩ J` -/

section Chain

attribute [local instance] unitizationOrder unitizationStarOrderedRing

variable {B : Type} [CStarAlgebra B]

/-- The inclusion `D ∩ J → D' ∩ J` for `D ≤ D'`. -/
def sepIncl (J : NonUnitalStarSubalgebra ℂ B) {D D' : StarSubalgebra ℂ B} (h : D ≤ D') :
    sepIdeal D J →⋆ₙₐ[ℂ] sepIdeal D' J :=
  NonUnitalStarSubalgebra.inclusion (sepIdeal_mono h)

theorem coe_sepIncl (J : NonUnitalStarSubalgebra ℂ B) {D D' : StarSubalgebra ℂ B}
    (h : D ≤ D') (x : sepIdeal D J) : ((sepIncl J h x : sepIdeal D' J) : B) = x :=
  rfl

theorem sepIncl_injective (J : NonUnitalStarSubalgebra ℂ B) {D D' : StarSubalgebra ℂ B}
    (h : D ≤ D') : Function.Injective (sepIncl J h) :=
  NonUnitalStarSubalgebra.inclusion_injective (sepIdeal_mono h)

theorem sepIncl_comp (J : NonUnitalStarSubalgebra ℂ B) {D D' D'' : StarSubalgebra ℂ B}
    (h : D ≤ D') (h' : D' ≤ D'') :
    (sepIncl J h').comp (sepIncl J h) = sepIncl J (h.trans h') :=
  NonUnitalStarAlgHom.ext fun _ => rfl

/-- Subtracting `inl x.fst + b` from `x ∈ S⁺` leaves the ideal element `x.snd - b`. -/
theorem sub_inl_fst_add_inr {S : Type*} [NonUnitalCStarAlgebra S] (x : Unitization ℂ S)
    (b : S) :
    x - (Unitization.inl x.fst + (b : Unitization ℂ S)) = ((x.snd - b : S) : Unitization ℂ S) := by
  calc x - (Unitization.inl x.fst + (b : Unitization ℂ S))
      = (Unitization.inl x.fst + (x.snd : Unitization ℂ S)) -
          (Unitization.inl x.fst + (b : Unitization ℂ S)) := by
        rw [Unitization.inl_fst_add_inr_snd_eq]
    _ = (x.snd : Unitization ℂ S) - (b : Unitization ℂ S) := add_sub_add_left_eq_sub _ _ _
    _ = ((x.snd - b : S) : Unitization ℂ S) := (Unitization.inr_sub (R := ℂ) _ _).symm

/-- **Continuity of `K₁` along the chain** (RLL 8.1 with 2.1.8). Every class of
`K₁(D_∞ ∩ J)`, `D_∞ = closure (⋃ₖ Dₖ)`, is the image of a class of `K₁(Dₖ ∩ J)` for some `k`.

Write the class as `[v]` with `v ∈ U_n((D_∞ ∩ J)⁺)`. The ideal parts of the entries of `v` are
approximated in some `Dₖ ∩ J` (`exists_sepIdeal_chain_near_fintype`). The resulting matrix `y`
over `(Dₖ ∩ J)⁺` has `‖v - y‖ ≤ 1/10` (`cStarMat_norm_le_sum_norm`), so its polar part `w`
has `[w] = [v]` (`exists_unitary_matMap_near`). -/
theorem exists_kOneN_map_eq_of_chain {J : NonUnitalStarSubalgebra ℂ B}
    (hJ : IsClosed (J : Set B)) (hideal : ∀ b x, x ∈ J → b * x ∈ J ∧ x * b ∈ J)
    {D : ℕ → StarSubalgebra ℂ B} (hmono : Monotone D) (hD : ∀ n, IsClosed (D n : Set B))
    [hDk : ∀ k, IsClosed (sepIdeal (D k) J : Set B)]
    [hDinf : IsClosed (sepIdeal (chainClosure D) J : Set B)]
    (x : KOneN (sepIdeal (chainClosure D) J)) :
    ∃ k, ∃ z : KOneN (sepIdeal (D k) J), KOneN.map (sepIncl J (le_chainClosure D k)) z = x := by
  obtain ⟨n, v, rfl⟩ := KOneN.exists_mk x
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 1 / (10 * ((n : ℝ) * n + 1)) := ⟨_, rfl⟩
  have hpos : 0 < 10 * ((n : ℝ) * n + 1) := by positivity
  have hε : 0 < ε := by
    rw [hεdef]
    exact one_div_pos.mpr hpos
  obtain ⟨k, z, hz, hzn⟩ := exists_sepIdeal_chain_near_fintype hJ hideal hmono hD
    (fun p : Fin n × Fin n => (((v : CStarMat n _) p.1 p.2).snd : B))
    (fun p => ((v : CStarMat n _) p.1 p.2).snd.2) hε
  have hψ : Function.Injective (Unitization.starMap (sepIncl J (le_chainClosure D k))) :=
    Unitization.starMap_injective (sepIncl_injective J _)
  obtain ⟨y, hy⟩ : ∃ y : CStarMat n (Unitization ℂ (sepIdeal (D k) J)), ∀ i j,
      y i j = Unitization.inl ((v : CStarMat n _) i j).fst +
        ((⟨z (i, j), hz (i, j)⟩ : sepIdeal (D k) J) : Unitization ℂ (sepIdeal (D k) J)) :=
    ⟨fun i j => Unitization.inl ((v : CStarMat n _) i j).fst +
      ((⟨z (i, j), hz (i, j)⟩ : sepIdeal (D k) J) : Unitization ℂ (sepIdeal (D k) J)),
      fun _ _ => rfl⟩
  have hψy : ∀ i j,
      matMapHom (Unitization.starMap (sepIncl J (le_chainClosure D k))) n y i j =
        Unitization.inl ((v : CStarMat n _) i j).fst +
          ((sepIncl J (le_chainClosure D k) ⟨z (i, j), hz (i, j)⟩ :
            sepIdeal (chainClosure D) J) : Unitization ℂ (sepIdeal (chainClosure D) J)) := by
    intro i j
    rw [matMapHom_apply, hy i j, map_add, Unitization.starMap_inr, Unitization.starMap_inl,
      Unitization.algebraMap_eq_inl]
  have hentry : ∀ i j, ‖((v : CStarMat n _) -
      matMapHom (Unitization.starMap (sepIncl J (le_chainClosure D k))) n y) i j‖ < ε := by
    intro i j
    have hsub : ((v : CStarMat n _) -
        matMapHom (Unitization.starMap (sepIncl J (le_chainClosure D k))) n y) i j =
        (((((v : CStarMat n _) i j).snd - sepIncl J (le_chainClosure D k) ⟨z (i, j), hz (i, j)⟩ :
          sepIdeal (chainClosure D) J)) : Unitization ℂ (sepIdeal (chainClosure D) J)) := by
      show (v : CStarMat n _) i j -
        matMapHom (Unitization.starMap (sepIncl J (le_chainClosure D k))) n y i j = _
      rw [hψy i j]
      exact sub_inl_fst_add_inr _ _
    rw [hsub, Unitization.norm_inr]
    exact hzn (i, j)
  have hnorm : ‖(v : CStarMat n _) -
      matMapHom (Unitization.starMap (sepIncl J (le_chainClosure D k))) n y‖ ≤ 1 / 10 := by
    calc ‖(v : CStarMat n _) -
          matMapHom (Unitization.starMap (sepIncl J (le_chainClosure D k))) n y‖
        ≤ ∑ j, ∑ i, ‖((v : CStarMat n _) -
          matMapHom (Unitization.starMap (sepIncl J (le_chainClosure D k))) n y) i j‖ :=
          cStarMat_norm_le_sum_norm _
      _ ≤ ∑ _j : Fin n, ∑ _i : Fin n, ε :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => (hentry i j).le
      _ = (n : ℝ) * n * ε := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ = (n : ℝ) * n / (10 * ((n : ℝ) * n + 1)) := by
          rw [hεdef]
          ring
      _ ≤ 1 / 10 := by
          rw [div_le_iff₀ hpos]
          linarith
  obtain ⟨w, hw⟩ := exists_unitary_matMap_near _ hψ v y hnorm
  refine ⟨k, KOneN.mk n w, ?_⟩
  rw [KOneN.map_mk]
  exact congrArg
    (fun c => KOneN.ofMul (kOneIota (Unitization ℂ (sepIdeal (chainClosure D) J)) n c)) hw

end Chain

end

end GroupApproximation.Full.TWWSchafhauser
