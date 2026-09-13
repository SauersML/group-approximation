import GroupApproximation.GGT.HullLemma35FreeFactors
import GroupApproximation.GGT.HullSCUnionGeometryAssembly
import GroupApproximation.Manuscript.NonMF.HullFiniteRadical
import GroupApproximation.Meta.AxiomGuard

/-!
# The free factors are suitable

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, arXiv:1308.4345, §7.
Hull's proof of Corollary 7.4 works in `F = G₁ ∗ G₂` after passing to `Gᵢ / K(Gᵢ)`, and it
applies Theorem 7.1 along the two factors.  This module proves the input that needs: over the
union of two Hull alphabets, the factor `Gᵢ` is suitable in `G₁ ∗ G₂` once `K(Gᵢ) = {1}`.

* Clause (1) of Hull's Definition 1.4 is `HullSC.actsNonElementarily_range_of_wordDist_eq`:
  the factor is isometrically embedded in the union alphabet.
* Clause (2) is `normalizesNoNontrivialFinite_range_inl`.  Let `F ≤ G₁ ∗ G₂` be finite and
  normalized by `G₁`.  Fix `x ∈ F`.  Since `G₁` is infinite and `F` is finite, two distinct
  `e₁, e₂ ∈ G₁` conjugate `x` to the same element.  So `x` commutes with the nontrivial letter
  `e₂⁻¹ e₁`, and a nontrivial letter of a free factor commutes only with elements of that factor
  (`mem_range_of_of_mul_eq_mul_of`).  So `F ≤ G₁`, and `F` is then a finite normal subgroup of
  `G₁`, which is trivial.

`exists_hullGeneratingSet_unionAlphabet` bundles the union alphabet as a `HullGeneratingSet` of
`G₁ ∗ G₂`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace HullFreeFactorSuitable

open Monoid
open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.GGT.FreeFactorsHypEmbedded (pairFam pairEquiv pairEquiv_inl pairEquiv_inr)

universe u

/-! ## Centralizers of letters in a free product -/

/-- **A nontrivial letter conjugates to a letter of its own factor only inside that factor.**
If `g, g' ∈ G i` are nontrivial and `g y = y g'`, then `y ∈ G i`.

Write `y = a · y'` with `a ∈ G i` and `y'` not beginning in `G i`.  If `y' ≠ 1`, then
`(a⁻¹ g a) · y' = y' · g'`.  The left side begins in `G i`, and the right side begins where `y'`
does. -/
theorem mem_range_of_of_mul_eq_mul_of {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] {i : ι}
    {g g' : G i} (hg : g ≠ 1) (hg' : g' ≠ 1) {y : CoprodI G}
    (hy : (CoprodI.of g : CoprodI G) * y = y * CoprodI.of g') :
    y ∈ (CoprodI.of : G i →* CoprodI G).range := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, p = CoprodI.Word.equivPair i (CoprodI.Word.equiv y) := ⟨_, rfl⟩
  have hrcons : CoprodI.Word.rcons p = CoprodI.Word.equiv y := by
    rw [hp]
    exact (CoprodI.Word.equivPair i).symm_apply_apply _
  have h1 : CoprodI.Word.prod (CoprodI.Word.equiv y) = y := CoprodI.Word.equiv.symm_apply_apply y
  have hy_eq : y = CoprodI.of p.head * CoprodI.Word.prod p.tail := by
    calc y = CoprodI.Word.prod (CoprodI.Word.equiv y) := h1.symm
      _ = CoprodI.Word.prod (CoprodI.Word.rcons p) := by rw [hrcons]
      _ = CoprodI.of p.head * CoprodI.Word.prod p.tail := CoprodI.Word.prod_rcons p
  have hhead' : GGT.RelHyp.headIdx (CoprodI.Word.prod p.tail) ≠ some i := by
    have he : CoprodI.Word.equiv (CoprodI.Word.prod p.tail) = p.tail :=
      CoprodI.Word.equiv.apply_symm_apply p.tail
    show CoprodI.Word.fstIdx (CoprodI.Word.equiv (CoprodI.Word.prod p.tail)) ≠ some i
    rw [he]
    exact p.fstIdx_ne
  by_cases hy1 : CoprodI.Word.prod p.tail = 1
  · refine MonoidHom.mem_range.mpr ⟨p.head, ?_⟩
    rw [hy_eq, hy1, mul_one]
  exfalso
  obtain ⟨g₁, hg₁def⟩ : ∃ g₁ : G i, g₁ = p.head⁻¹ * g * p.head := ⟨_, rfl⟩
  have hg₁ : g₁ ≠ 1 := by
    rw [hg₁def]
    intro h
    apply hg
    have h' := congrArg (fun x => p.head * x * p.head⁻¹) h
    simpa [mul_assoc] using h'
  have hconj : (CoprodI.of g₁ : CoprodI G) * CoprodI.Word.prod p.tail
      = CoprodI.Word.prod p.tail * CoprodI.of g' := by
    have hy2 := hy
    rw [hy_eq] at hy2
    rw [hg₁def, map_mul, map_mul, map_inv]
    calc (CoprodI.of p.head)⁻¹ * CoprodI.of g * CoprodI.of p.head * CoprodI.Word.prod p.tail
        = (CoprodI.of p.head)⁻¹
            * (CoprodI.of g * (CoprodI.of p.head * CoprodI.Word.prod p.tail)) := by
          simp only [mul_assoc]
      _ = (CoprodI.of p.head)⁻¹
            * (CoprodI.of p.head * CoprodI.Word.prod p.tail * CoprodI.of g') := by
          rw [hy2]
      _ = CoprodI.Word.prod p.tail * CoprodI.of g' := by
          simp only [mul_assoc, inv_mul_cancel_left]
  have hL : GGT.RelHyp.headIdx ((CoprodI.of g₁ : CoprodI G) * CoprodI.Word.prod p.tail)
      = some i := by
    have hlist : (CoprodI.Word.equiv
        ((CoprodI.of g₁ : CoprodI G) * CoprodI.Word.prod p.tail)).toList
        = (⟨i, g₁⟩ : Σ i, G i) :: (CoprodI.Word.equiv (CoprodI.Word.prod p.tail)).toList := by
      rw [FreeProductCyclic.equiv_of_mul]
      exact GGT.RelHyp.toList_of_smul_of_fstIdx_ne hg₁ hhead'
    simp [GGT.RelHyp.headIdx_eq, hlist]
  have hne : CoprodI.Word.prod p.tail * (CoprodI.of g' : CoprodI G) ≠ 1 := by
    intro h
    apply hhead'
    have hinv : CoprodI.Word.prod p.tail = CoprodI.of g'⁻¹ := by
      rw [map_inv]
      exact mul_eq_one_iff_eq_inv.mp h
    rw [hinv]
    exact GGT.RelHyp.headIdx_of (inv_ne_one.mpr hg')
  have hR := GGT.RelHyp.headIdx_mul_of g' hy1 hne
  rw [← hconj, hL] at hR
  exact hhead' hR.symm

#audit_axioms mem_range_of_of_mul_eq_mul_of

/-! ## The two factors of `G₁ ∗ G₂` -/

section Coprod

variable {G₁ G₂ : Type u} [Group G₁] [Group G₂]

/-- A nontrivial element of `G₁` conjugates to an element of `G₁` only inside `G₁`. -/
theorem mem_range_inl_of_inl_mul_eq {a a' : G₁} (ha : a ≠ 1) (ha' : a' ≠ 1)
    {y : Monoid.Coprod G₁ G₂}
    (hy : (Monoid.Coprod.inl a : Monoid.Coprod G₁ G₂) * y = y * Monoid.Coprod.inl a') :
    y ∈ (Monoid.Coprod.inl : G₁ →* Monoid.Coprod G₁ G₂).range := by
  have hy' := congrArg (pairEquiv (G₁ := G₁) (G₂ := G₂)) hy
  rw [map_mul, map_mul, pairEquiv_inl, pairEquiv_inl] at hy'
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp
    (mem_range_of_of_mul_eq_mul_of (G := pairFam G₁ G₂) (i := false) ha ha' hy')
  refine MonoidHom.mem_range.mpr ⟨z, pairEquiv.injective ?_⟩
  rw [pairEquiv_inl]
  exact hz

#audit_axioms mem_range_inl_of_inl_mul_eq

/-- A nontrivial element of `G₂` conjugates to an element of `G₂` only inside `G₂`. -/
theorem mem_range_inr_of_inr_mul_eq {b b' : G₂} (hb : b ≠ 1) (hb' : b' ≠ 1)
    {y : Monoid.Coprod G₁ G₂}
    (hy : (Monoid.Coprod.inr b : Monoid.Coprod G₁ G₂) * y = y * Monoid.Coprod.inr b') :
    y ∈ (Monoid.Coprod.inr : G₂ →* Monoid.Coprod G₁ G₂).range := by
  have hy' := congrArg (pairEquiv (G₁ := G₁) (G₂ := G₂)) hy
  rw [map_mul, map_mul, pairEquiv_inr, pairEquiv_inr] at hy'
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp
    (mem_range_of_of_mul_eq_mul_of (G := pairFam G₁ G₂) (i := true) hb hb' hy')
  refine MonoidHom.mem_range.mpr ⟨z, pairEquiv.injective ?_⟩
  rw [pairEquiv_inr]
  exact hz

#audit_axioms mem_range_inr_of_inr_mul_eq

/-- **Clause (2) of Hull's Definition 1.4 for the left factor.**  If `G₁` is infinite and has no
nontrivial finite normal subgroup, then `G₁` normalizes no nontrivial finite subgroup of
`G₁ ∗ G₂`. -/
theorem normalizesNoNontrivialFinite_range_inl [Infinite G₁] (hK : HasTrivialFiniteRadical G₁) :
    HullSuitable.NormalizesNoNontrivialFinite
      (Monoid.Coprod.inl : G₁ →* Monoid.Coprod G₁ G₂).range := by
  intro F hF hnorm
  have hconj : ∀ (e : G₁) (x : Monoid.Coprod G₁ G₂), x ∈ F →
      Monoid.Coprod.inl e * x * (Monoid.Coprod.inl e)⁻¹ ∈ F :=
    fun e x hx => hnorm _ (MonoidHom.mem_range.mpr ⟨e, rfl⟩) x hx
  have hmem : ∀ x ∈ F, x ∈ (Monoid.Coprod.inl : G₁ →* Monoid.Coprod G₁ G₂).range := by
    intro x hx
    obtain ⟨e₁, e₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun e : G₁ => (⟨Monoid.Coprod.inl e * x * (Monoid.Coprod.inl e)⁻¹, hconj e x hx⟩ : F))
    have h1 : (Monoid.Coprod.inl e₁ : Monoid.Coprod G₁ G₂) * x * (Monoid.Coprod.inl e₁)⁻¹
        = Monoid.Coprod.inl e₂ * x * (Monoid.Coprod.inl e₂)⁻¹ := congrArg Subtype.val heq
    have hc : (Monoid.Coprod.inl (e₂⁻¹ * e₁) : Monoid.Coprod G₁ G₂) * x
        = x * Monoid.Coprod.inl (e₂⁻¹ * e₁) := by
      have h2 := congrArg (fun z => (Monoid.Coprod.inl e₂ : Monoid.Coprod G₁ G₂)⁻¹ * z
        * Monoid.Coprod.inl e₁) h1
      simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] at h2
      rw [map_mul, map_inv]
      simpa only [mul_assoc] using h2
    have hg : e₂⁻¹ * e₁ ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
    exact mem_range_inl_of_inl_mul_eq hg hg hc
  have hcomap : F.comap (Monoid.Coprod.inl : G₁ →* Monoid.Coprod G₁ G₂) = ⊥ := by
    refine hK _ ⟨fun n hn g => ?_⟩ ?_
    · show Monoid.Coprod.inl (g * n * g⁻¹) ∈ F
      rw [map_mul, map_mul, map_inv]
      exact hconj g (Monoid.Coprod.inl n) hn
    · exact Finite.of_injective
        (fun n : F.comap (Monoid.Coprod.inl : G₁ →* Monoid.Coprod G₁ G₂) =>
          (⟨Monoid.Coprod.inl (n : G₁), n.2⟩ : F))
        (fun n₁ n₂ h => Subtype.ext (Monoid.Coprod.inl_injective (congrArg Subtype.val h)))
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp (hmem x hx)
  have he : e ∈ F.comap (Monoid.Coprod.inl : G₁ →* Monoid.Coprod G₁ G₂) := hx
  rw [hcomap, Subgroup.mem_bot] at he
  rw [he, map_one]

#audit_axioms normalizesNoNontrivialFinite_range_inl

/-- **Clause (2) of Hull's Definition 1.4 for the right factor.** -/
theorem normalizesNoNontrivialFinite_range_inr [Infinite G₂] (hK : HasTrivialFiniteRadical G₂) :
    HullSuitable.NormalizesNoNontrivialFinite
      (Monoid.Coprod.inr : G₂ →* Monoid.Coprod G₁ G₂).range := by
  intro F hF hnorm
  have hconj : ∀ (e : G₂) (x : Monoid.Coprod G₁ G₂), x ∈ F →
      Monoid.Coprod.inr e * x * (Monoid.Coprod.inr e)⁻¹ ∈ F :=
    fun e x hx => hnorm _ (MonoidHom.mem_range.mpr ⟨e, rfl⟩) x hx
  have hmem : ∀ x ∈ F, x ∈ (Monoid.Coprod.inr : G₂ →* Monoid.Coprod G₁ G₂).range := by
    intro x hx
    obtain ⟨e₁, e₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun e : G₂ => (⟨Monoid.Coprod.inr e * x * (Monoid.Coprod.inr e)⁻¹, hconj e x hx⟩ : F))
    have h1 : (Monoid.Coprod.inr e₁ : Monoid.Coprod G₁ G₂) * x * (Monoid.Coprod.inr e₁)⁻¹
        = Monoid.Coprod.inr e₂ * x * (Monoid.Coprod.inr e₂)⁻¹ := congrArg Subtype.val heq
    have hc : (Monoid.Coprod.inr (e₂⁻¹ * e₁) : Monoid.Coprod G₁ G₂) * x
        = x * Monoid.Coprod.inr (e₂⁻¹ * e₁) := by
      have h2 := congrArg (fun z => (Monoid.Coprod.inr e₂ : Monoid.Coprod G₁ G₂)⁻¹ * z
        * Monoid.Coprod.inr e₁) h1
      simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] at h2
      rw [map_mul, map_inv]
      simpa only [mul_assoc] using h2
    have hg : e₂⁻¹ * e₁ ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
    exact mem_range_inr_of_inr_mul_eq hg hg hc
  have hcomap : F.comap (Monoid.Coprod.inr : G₂ →* Monoid.Coprod G₁ G₂) = ⊥ := by
    refine hK _ ⟨fun n hn g => ?_⟩ ?_
    · show Monoid.Coprod.inr (g * n * g⁻¹) ∈ F
      rw [map_mul, map_mul, map_inv]
      exact hconj g (Monoid.Coprod.inr n) hn
    · exact Finite.of_injective
        (fun n : F.comap (Monoid.Coprod.inr : G₂ →* Monoid.Coprod G₁ G₂) =>
          (⟨Monoid.Coprod.inr (n : G₂), n.2⟩ : F))
        (fun n₁ n₂ h => Subtype.ext (Monoid.Coprod.inr_injective (congrArg Subtype.val h)))
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp (hmem x hx)
  have he : e ∈ F.comap (Monoid.Coprod.inr : G₂ →* Monoid.Coprod G₁ G₂) := hx
  rw [hcomap, Subgroup.mem_bot] at he
  rw [he, map_one]

#audit_axioms normalizesNoNontrivialFinite_range_inr

end Coprod

/-! ## Suitability over the union alphabet -/

/-- A group with a Hull generating set is infinite. -/
theorem infinite_of_hullGeneratingSet {G : Type u} [Group G] (A : HullGeneratingSet G) :
    Infinite G := by
  haveI := HullGeometry.infinite_of_actsNonElementarily A.nonElementary
  exact Infinite.of_injective (fun x : (⊤ : Subgroup G) => (x : G)) Subtype.val_injective

section Union

variable {E H : Type} [Group E] [Group H]

/-- **The union alphabet is a Hull generating set of `E ∗ H`.** -/
theorem exists_hullGeneratingSet_unionAlphabet (A : HullGeneratingSet E)
    (B : HullGeneratingSet H) :
    ∃ C : HullGeneratingSet (Monoid.Coprod E H),
      C.alphabet = HullSC.unionAlphabet A.alphabet B.alphabet := by
  have hcar : (HullSC.unionAlphabet A.alphabet B.alphabet).carrier
      = HullSC.UnionCarrier A.alphabet B.alphabet := rfl
  obtain ⟨δ, hδ⟩ := HullSCUnionGeometry.exists_isHyperbolicSpace_cayley_unionAlphabet A B
  exact ⟨⟨HullSC.unionAlphabet A.alphabet B.alphabet, δ, hδ,
    HullSCUnionGeometry.isAcylindrical_unionAlphabet A B,
    HullSC.actsNonElementarily_top_of_subgroup
      (HullSC.actsNonElementarily_range_of_wordDist_eq
        (Monoid.Coprod.inl : E →* Monoid.Coprod E H) (HullSC.wordDist_inl_eq hcar)
        A.nonElementary)⟩, rfl⟩

#audit_axioms exists_hullGeneratingSet_unionAlphabet

/-- **The left factor is suitable** over the union alphabet once `K(E) = {1}`. -/
theorem suitable_range_inl (A : HullGeneratingSet E) (B : HullGeneratingSet H)
    (hE : HasTrivialFiniteRadical E) :
    Suitable (HullSC.unionAlphabet A.alphabet B.alphabet)
      (Monoid.Coprod.inl : E →* Monoid.Coprod E H).range := by
  have hcar : (HullSC.unionAlphabet A.alphabet B.alphabet).carrier
      = HullSC.UnionCarrier A.alphabet B.alphabet := rfl
  haveI : Infinite E := infinite_of_hullGeneratingSet A
  exact ⟨HullSC.actsNonElementarily_range_of_wordDist_eq
      (Monoid.Coprod.inl : E →* Monoid.Coprod E H) (HullSC.wordDist_inl_eq hcar)
      A.nonElementary,
    normalizesNoNontrivialFinite_range_inl hE⟩

#audit_axioms suitable_range_inl

/-- **The right factor is suitable** over the union alphabet once `K(H) = {1}`. -/
theorem suitable_range_inr (A : HullGeneratingSet E) (B : HullGeneratingSet H)
    (hH : HasTrivialFiniteRadical H) :
    Suitable (HullSC.unionAlphabet A.alphabet B.alphabet)
      (Monoid.Coprod.inr : H →* Monoid.Coprod E H).range := by
  have hcar : (HullSC.unionAlphabet A.alphabet B.alphabet).carrier
      = HullSC.UnionCarrier A.alphabet B.alphabet := rfl
  haveI : Infinite H := infinite_of_hullGeneratingSet B
  exact ⟨HullSC.actsNonElementarily_range_of_wordDist_eq
      (Monoid.Coprod.inr : H →* Monoid.Coprod E H) (HullSC.wordDist_inr_eq hcar)
      B.nonElementary,
    normalizesNoNontrivialFinite_range_inr hH⟩

#audit_axioms suitable_range_inr

end Union

end HullFreeFactorSuitable
end NonMF
end Manuscript
end GroupApproximation
