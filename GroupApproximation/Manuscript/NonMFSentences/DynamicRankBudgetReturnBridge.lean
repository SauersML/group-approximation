import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudgetReturnKernel
import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudget
import GroupApproximation.Dynamics.ReturnTowerCrossedProduct
import GroupApproximation.Dynamics.ReturnRingUnit
import GroupApproximation.Dynamics.InvolutionLocalizationStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:dynamic-rank-budget`: the return embeddings from their pieces

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`), tex 1707–1757.  This module proves the residual
`ReturnEmbeddingStatement` of `DynamicRankBudget` over four pieces:

* `ReturnRingCrossedProductStatement` (tex 1723–1726, ct-return-tower): `P_C ≅ LC(C,k) ⋊_{S_C} ℤ`;
* `ClopenCrossedProduct.InvolutionLocalizationMatrixClause` (the `F₂` clause of
  `lem:involution-localization`, tex 1667–1669, ct-involution);
* `ClopenCrossedProduct.CoreKernelElementaryStatement` (tex 1638–1639: `K_n(I) ⊆ EL_n(R_X)` over `F₂`,
  `n ≥ 2`), for the elementary clause;
* `ReturnTransientIdealStatement` (tex 1750, "The return transient ideal is therefore $J=p_CIp_C$", the
  inclusion `θ⁻¹(p_C I p_C) ⊆ I_C`; ct-rank-budget).

The rest is closed: the section construction `exists_isReturnSection` and the tower
`returnTowerUnits` (ct-return-tower), the embeddings of `Algebra/ReturnTowerEmbeddings`
(ct-bilateral-mf), the phase-zero placement and its transport (`DynamicRankBudgetPlacement`,
`DynamicRankBudgetReturnKernel`), and here the zeroth levels `a_0 = b_0 = p_C`
(`returnTowerUnits_a_zero`, tex 1734 "For $i<r$ we have $D_i=C$").

The printed return system is `(C, S_C)`, with `C` the section of `exists_isReturnSection` and
`S_C = firstReturnHomeomorph hC`.
-/

namespace GroupApproximation.ChainCore.DynamicRankBudget

open MFQuotientUnits ReturnTowerUnits

/-! ## Periods and sections -/

section Sections

variable {X : Type*} [TopologicalSpace X]

theorem zpow_natCast_apply_eq_iterate (T : X ≃ₜ X) (j : ℕ) (x : X) :
    (T ^ (j : ℤ)) x = (⇑T)^[j] x := by
  induction j generalizing x with
  | zero => rw [Nat.cast_zero, zpow_zero, Homeomorph.one_apply, Function.iterate_zero, id_eq]
  | succ j ih =>
    rw [Nat.cast_succ, zpow_add_one, Homeomorph.mul_apply, ih, Function.iterate_succ_apply]

theorem noShortPeriods_of_iterate {T : X ≃ₜ X} {r : ℕ}
    (h : ∀ (x : X) (j : ℕ), 0 < j → j < r → (⇑T)^[j] x ≠ x) : NoShortPeriods T r := by
  intro x j hj0 hjr
  rw [zpow_natCast_apply_eq_iterate]
  exact h x j hj0 hjr

/-- A return section meets every orbit. -/
theorem isReturnSection_exists_zpow_mem {T : X ≃ₜ X} {r : ℕ} {C : Set X}
    (hC : IsReturnSection T r C) (x : X) : ∃ j : ℤ, (T ^ j) x ∈ C := by
  obtain ⟨j, -, hx⟩ := hC.exists_mem_image x
  exact ⟨-j, (mem_zpow_image_iff j).1 hx⟩

end Sections

/-! ## The zeroth levels of the dynamical tower -/

section Levels

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {r : ℕ} {C : Set X} (k : Type*) [Ring k]
  (hC : IsReturnSection T r C)

/-- `a_0 = u^0 1_{D_0} = 1_C = p_C` (tex 1734, "For $i<r$ we have $D_i=C$"). -/
theorem returnTowerUnits_a_zero (hr : 1 ≤ r) (hr0 : 0 < r) :
    (returnTowerUnits k hC hr).a ((returnTowerUnits k hC hr).lo ⟨0, hr0⟩) =
      (returnTowerUnits k hC hr).p := by
  show towerA k hC 0 = ClopenCrossedProduct.coeff T k (LocallyConstant.charFn k hC.isClopen)
  rw [towerA, levelCoeff, charFn_towerLevel_of_lt k hC hr0, Nat.cast_zero, unitPow_zero, one_mul]

/-- `b_0 = 1_{D_0} u^0 = 1_C = p_C`. -/
theorem returnTowerUnits_b_zero (hr : 1 ≤ r) (hr0 : 0 < r) :
    (returnTowerUnits k hC hr).b ((returnTowerUnits k hC hr).lo ⟨0, hr0⟩) =
      (returnTowerUnits k hC hr).p := by
  show towerB k hC 0 = ClopenCrossedProduct.coeff T k (LocallyConstant.charFn k hC.isClopen)
  rw [towerB, levelCoeff, charFn_towerLevel_of_lt k hC hr0, Nat.cast_zero, neg_zero, unitPow_zero,
    mul_one]

end Levels

/-! ## Matrix helpers -/

section Helpers

variable {A B : Type*} [Ring A] [Ring B]

/-- A deviation of the printed form `p_C a p_C` with `a ∈ I` is a corner deviation with entries in `I`. -/
theorem isCornerDeviation_and_mem_of_eq {N r : ℕ} (τ : ReturnTowerUnits A N r) {n : Type*}
    [DecidableEq n] (I : TwoSidedIdeal A) (M : Matrix n n A)
    (h : ∀ i j, ∃ a ∈ I, M i j - (1 : Matrix n n A) i j = τ.p * a * τ.p) :
    IsCornerDeviation τ M ∧ ∀ i j, (M - 1) i j ∈ I := by
  have hp : τ.p * τ.p = τ.p := τ.isIdempotentElem_p.eq
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · obtain ⟨a, -, ha⟩ := h i j
    rw [Matrix.sub_apply, ha]
    constructor
    · calc τ.p * (τ.p * a * τ.p) = (τ.p * τ.p) * a * τ.p := by simp only [mul_assoc]
        _ = τ.p * a * τ.p := by rw [hp]
    · calc τ.p * a * τ.p * τ.p = τ.p * a * (τ.p * τ.p) := by simp only [mul_assoc]
        _ = τ.p * a * τ.p := by rw [hp]
  · obtain ⟨a, haI, ha⟩ := h i j
    rw [Matrix.sub_apply, ha]
    exact I.mul_mem_right _ _ (I.mul_mem_left _ _ haI)

theorem units_map_matrixFinOneEntry_scalar (c : Aˣ) :
    Units.map (matrixFinOneEntry A) (Units.map (Matrix.scalar (Fin 1)).toMonoidHom c) = c :=
  Units.ext (by
    show (Matrix.scalar (Fin 1) (c : A)) 0 0 = (c : A)
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq])

theorem units_map_mapMatrix_scalar (f : A →+* B) (c : Aˣ) :
    Units.map (RingHom.mapMatrix f).toMonoidHom (Units.map (Matrix.scalar (Fin 1)).toMonoidHom c) =
      Units.map (Matrix.scalar (Fin 1)).toMonoidHom (Units.map f.toMonoidHom c) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show ((Matrix.scalar (Fin 1) (c : A)).map f) i j = Matrix.scalar (Fin 1) (f c) i j
  rw [Matrix.map_apply, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero f

theorem units_map_mapMatrix_reindex_symm {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (f : A →+* B) (e : ι ≃ κ) (u : (Matrix κ κ A)ˣ) :
    Units.map (RingHom.mapMatrix f).toMonoidHom ((elementaryReindexUnitEquiv (R := A) e).symm u) =
      (elementaryReindexUnitEquiv (R := B) e).symm
        (Units.map (RingHom.mapMatrix f).toMonoidHom u) :=
  Units.ext (Matrix.ext fun _ _ => rfl)

end Helpers

/-! ## The piece `J = p_C I p_C` -/

/-- **Piece: `θ⁻¹(p_C I p_C)` lies in the return transient ideal** (tex 1750, "The return transient
ideal is therefore $J=p_CIp_C$", the inclusion used at tex 1752–1757; owner ct-rank-budget).  For a
return section `C` and any ring isomorphism `θ : R_C ≅ p_C R_X p_C` with the two properties of
`ReturnRingCrossedProductStatement` (coefficients go to their extensions by zero; the unit goes to
`v = ∑_h u^h 1_{C_h}`), an element whose image lies in the transient ideal `I` of `R_X` lies in the
transient ideal of the return system `(C, S_C)`. -/
def ReturnTransientIdealStatement : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (r : ℕ) (C : Set X) (hC : IsReturnSection T r C), 1 ≤ r → ∀ [CompactSpace C]
    (k : Type) [Field k] [Finite k]
    (hp : IsIdempotentElem
      (ClopenCrossedProduct.coeff T k (LocallyConstant.charFn k hC.isClopen)))
    (θ : ClopenCrossedProduct (firstReturnHomeomorph hC) k ≃+*
      Corner (ClopenCrossedProduct T k)
        (ClopenCrossedProduct.coeff T k (LocallyConstant.charFn k hC.isClopen)) hp),
    (∀ (f : LocallyConstant C k) (g : LocallyConstant X k),
        (∀ x : C, g x = f x) → (∀ x : X, x ∉ C → g x = 0) →
          ((θ (ClopenCrossedProduct.coeff (firstReturnHomeomorph hC) k f) :
            ClopenCrossedProduct T k)) = ClopenCrossedProduct.coeff T k g) →
    (∃ v : ℕ → LocallyConstant X k,
        (∀ (h : ℕ) (x : X), v h x = Set.indicator {y | y ∈ C ∧ returnTime T C y = h} 1 x) ∧
        ((θ ((ClopenCrossedProduct.unit (firstReturnHomeomorph hC) k :
            (ClopenCrossedProduct (firstReturnHomeomorph hC) k)ˣ) :
              ClopenCrossedProduct (firstReturnHomeomorph hC) k) : ClopenCrossedProduct T k)) =
          ∑ h ∈ Finset.range (2 * r),
            ((ClopenCrossedProduct.unit T k ^ (h : ℤ) : (ClopenCrossedProduct T k)ˣ) :
              ClopenCrossedProduct T k) * ClopenCrossedProduct.coeff T k (v h)) →
    ∀ c : ClopenCrossedProduct (firstReturnHomeomorph hC) k,
      ((θ c : Corner (ClopenCrossedProduct T k)
          (ClopenCrossedProduct.coeff T k (LocallyConstant.charFn k hC.isClopen)) hp) :
          ClopenCrossedProduct T k) ∈ ClopenCrossedProduct.coreTransientIdeal T k →
        c ∈ ClopenCrossedProduct.coreTransientIdeal (firstReturnHomeomorph hC) k

/-! ## The return embeddings -/

/-- **The return embeddings of `cor:dynamic-rank-budget`, over their pieces** (tex 1707–1757).

The return system is the section `C` of `exists_isReturnSection` with `S_C = firstReturnHomeomorph hC`.
Over every finite field the tower gives the four embeddings (`returnEmbeddingClauses`).  Over `F₂`,
an element `x` of a core kernel is conjugated by the involution `w I_n` of
`lem:involution-localization` to `g` with deviation `p_C a p_C`, `a ∈ I`.  The phase-zero placement
of `g`, carried back along the block transport, lies in the core kernel of the return system by
`ReturnTransientIdealStatement`, and the embedding sends it to `g` (tex 1752–1757). -/
theorem returnEmbeddingStatement_of_pieces (hring : ReturnRingCrossedProductStatement)
    (hinv : ClopenCrossedProduct.InvolutionLocalizationMatrixClause)
    (hkerEL : ClopenCrossedProduct.CoreKernelElementaryStatement)
    (hJ : ReturnTransientIdealStatement) : ReturnEmbeddingStatement := by
  intro X _ _ _ _ T r hr hper
  obtain ⟨C, hC⟩ := exists_isReturnSection hr (noShortPeriods_of_iterate hper)
  have hCc : CompactSpace C := isCompact_iff_compactSpace.mp hC.isClopen.isClosed.isCompact
  have hr0 : 0 < r := by omega
  have hcover : ∀ x : X, ∃ j : ℤ, (T ^ j) x ∈ C := isReturnSection_exists_zpow_mem hC
  have hCn : Nonempty C := by
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨j, hj⟩ := hcover x
    exact ⟨⟨_, hj⟩⟩
  have hbound : ∃ H : ℕ, ∀ x ∈ C, ∃ h : ℕ, 0 < h ∧ h ≤ H ∧ (T ^ (h : ℤ)) x ∈ C :=
    ⟨2 * r - 1, fun x _ => hC.exists_return x⟩
  refine ⟨C, inferInstance, hCc, inferInstance, hCn, firstReturnHomeomorph hC, ?_, ?_, ?_, ?_⟩
  · intro k _ _
    obtain ⟨S, hp, θ, hS, -, -⟩ := hring X T k r C hC hr
    obtain rfl : S = firstReturnHomeomorph hC :=
      Homeomorph.ext fun x => Subtype.ext (by rw [hS, firstReturnHomeomorph_apply])
    exact returnEmbeddingClauses (returnTowerUnits k hC hr) θ
  · intro n hn
    obtain ⟨S, hp, θ, hS, hcoef, hunit⟩ := hring X T (ZMod 2) r C hC hr
    obtain rfl : S = firstReturnHomeomorph hC :=
      Homeomorph.ext fun x => Subtype.ext (by rw [hS, firstReturnHomeomorph_apply])
    have hJθ := hJ X T r C hC hr (ZMod 2) hp θ hcoef hunit
    have ha := returnTowerUnits_a_zero (ZMod 2) hC hr hr0
    have hb := returnTowerUnits_b_zero (ZMod 2) hC hr hr0
    refine ⟨(returnTowerUnits (ZMod 2) hC hr).glEmbedding θ n, fun x hx => ?_⟩
    obtain ⟨w, -, -, hconj, -⟩ := hinv X T C hC.isClopen hcover hbound n {x}
      (fun G hG => by
        rw [Finset.mem_singleton] at hG; subst hG; exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hx))
    obtain ⟨hgc, hgI⟩ := isCornerDeviation_and_mem_of_eq (returnTowerUnits (ZMod 2) hC hr)
      (ClopenCrossedProduct.coreTransientIdeal T (ZMod 2)) _ (hconj x (Finset.mem_singleton_self x))
    exact ⟨Units.map (Matrix.scalar (Fin n)).toMonoidHom w, Subgroup.mem_map.2
      ⟨((returnTowerUnits (ZMod 2) hC hr).blockTransport θ n).symm
          (placementUnit (returnTowerUnits (ZMod 2) hC hr) hr0 ha hb _ hgc),
        MonoidHom.mem_ker.2 (units_map_mapMatrix_eq_one_of_forall_mem_ker _ _
          (returnPlacement_sub_one_mem (returnTowerUnits (ZMod 2) hC hr) θ n hr0 ha hb _ hgc _ _
            hgI hJθ)),
        glEmbedding_returnPlacement (returnTowerUnits (ZMod 2) hC hr) θ n hr0 ha hb _ hgc⟩⟩
  · intro n hn
    obtain ⟨S, hp, θ, hS, hcoef, hunit⟩ := hring X T (ZMod 2) r C hC hr
    obtain rfl : S = firstReturnHomeomorph hC :=
      Homeomorph.ext fun x => Subtype.ext (by rw [hS, firstReturnHomeomorph_apply])
    have hJθ := hJ X T r C hC hr (ZMod 2) hp θ hcoef hunit
    have ha := returnTowerUnits_a_zero (ZMod 2) hC hr hr0
    have hb := returnTowerUnits_b_zero (ZMod 2) hC hr hr0
    refine ⟨(returnTowerUnits (ZMod 2) hC hr).elEmbedding θ n hn, fun x hx => ?_⟩
    obtain ⟨w, -, -, hconj, hEL⟩ := hinv X T C hC.isClopen hcover hbound n
      {(x : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ)}
      (fun G hG => by
        rw [Finset.mem_singleton] at hG; subst hG; exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hx))
    obtain ⟨hgc, hgI⟩ := isCornerDeviation_and_mem_of_eq (returnTowerUnits (ZMod 2) hC hr)
      (ClopenCrossedProduct.coreTransientIdeal T (ZMod 2)) _ (hconj _ (Finset.mem_singleton_self _))
    have hy : ((returnTowerUnits (ZMod 2) hC hr).blockTransport θ n).symm
          (placementUnit (returnTowerUnits (ZMod 2) hC hr) hr0 ha hb _ hgc) ∈
        glCoreKernel (firstReturnHomeomorph hC) (ZMod 2) (n * r) :=
      MonoidHom.mem_ker.2 (units_map_mapMatrix_eq_one_of_forall_mem_ker _ _
        (returnPlacement_sub_one_mem (returnTowerUnits (ZMod 2) hC hr) θ n hr0 ha hb _ hgc _ _
          hgI hJθ))
    have hyEL := hkerEL C (firstReturnHomeomorph hC) (n * r) (by nlinarith) hy
    refine ⟨⟨_, hEL hn⟩, Subgroup.mem_map.2
      ⟨⟨_, hyEL⟩, MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hy), ?_⟩⟩
    refine Subtype.ext ?_
    rw [coe_elEmbedding]
    exact glEmbedding_returnPlacement (returnTowerUnits (ZMod 2) hC hr) θ n hr0 ha hb _ hgc
  · obtain ⟨S, hp, θ, hS, hcoef, hunit⟩ := hring X T (ZMod 2) r C hC hr
    obtain rfl : S = firstReturnHomeomorph hC :=
      Homeomorph.ext fun x => Subtype.ext (by rw [hS, firstReturnHomeomorph_apply])
    have hJθ := hJ X T r C hC hr (ZMod 2) hp θ hcoef hunit
    have ha := returnTowerUnits_a_zero (ZMod 2) hC hr hr0
    have hb := returnTowerUnits_b_zero (ZMod 2) hC hr hr0
    refine ⟨(returnTowerUnits (ZMod 2) hC hr).unitEmbedding θ, fun x hx => ?_⟩
    have hx1 : Units.map (Matrix.scalar (Fin 1)).toMonoidHom x ∈
        (ClopenCrossedProduct.coreRestrictMatrixUnits T (ZMod 2) 1).ker := by
      refine MonoidHom.mem_ker.2 ?_
      change Units.map (RingHom.mapMatrix (coreRestrict T (ZMod 2))).toMonoidHom
        (Units.map (Matrix.scalar (Fin 1)).toMonoidHom x) = 1
      rw [units_map_mapMatrix_scalar,
        show Units.map (coreRestrict T (ZMod 2)).toMonoidHom x = 1 from MonoidHom.mem_ker.1 hx,
        map_one]
    obtain ⟨w, -, -, hconj, -⟩ := hinv X T C hC.isClopen hcover hbound 1
      {Units.map (Matrix.scalar (Fin 1)).toMonoidHom x}
      (fun G hG => by rw [Finset.mem_singleton] at hG; subst hG; exact hx1)
    obtain ⟨hgc, hgI⟩ := isCornerDeviation_and_mem_of_eq (returnTowerUnits (ZMod 2) hC hr)
      (ClopenCrossedProduct.coreTransientIdeal T (ZMod 2)) _ (hconj _ (Finset.mem_singleton_self _))
    have hy1 := units_map_mapMatrix_eq_one_of_forall_mem_ker
      (coreRestrict (firstReturnHomeomorph hC) (ZMod 2)) _
      (returnPlacement_sub_one_mem (returnTowerUnits (ZMod 2) hC hr) θ 1 hr0 ha hb _ hgc _ _ hgI
        hJθ)
    refine ⟨w, Subgroup.mem_map.2 ⟨(elementaryReindexUnitEquiv
        (R := ClopenCrossedProduct (firstReturnHomeomorph hC) (ZMod 2))
        (finCongr (Nat.one_mul r).symm)).symm
          (((returnTowerUnits (ZMod 2) hC hr).blockTransport θ 1).symm
            (placementUnit (returnTowerUnits (ZMod 2) hC hr) hr0 ha hb _ hgc)), ?_, ?_⟩⟩
    · exact MonoidHom.mem_ker.2
        ((units_map_mapMatrix_reindex_symm (coreRestrict (firstReturnHomeomorph hC) (ZMod 2))
          (finCongr (Nat.one_mul r).symm) _).trans (by rw [hy1, map_one]))
    · rw [unitEmbedding_apply, MulEquiv.apply_symm_apply,
        glEmbedding_returnPlacement (returnTowerUnits (ZMod 2) hC hr) θ 1 hr0 ha hb _ hgc,
        map_mul, map_mul, map_inv, units_map_matrixFinOneEntry_scalar,
        units_map_matrixFinOneEntry_scalar]

end GroupApproximation.ChainCore.DynamicRankBudget

/-! ### Audit -/

#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.zpow_natCast_apply_eq_iterate
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.noShortPeriods_of_iterate
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.isReturnSection_exists_zpow_mem
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.returnTowerUnits_a_zero
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.returnTowerUnits_b_zero
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.isCornerDeviation_and_mem_of_eq
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.units_map_matrixFinOneEntry_scalar
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.units_map_mapMatrix_scalar
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.units_map_mapMatrix_reindex_symm
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.returnEmbeddingStatement_of_pieces
