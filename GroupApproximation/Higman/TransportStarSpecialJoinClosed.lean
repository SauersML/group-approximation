import GroupApproximation.Higman.BenignJoinExactGenerated
import GroupApproximation.Higman.BenignJoinFiniteQuotientMap
import GroupApproximation.Higman.HNNSubextensionFiniteBaseProfinite
import GroupApproximation.Higman.FreeLampFiniteBaseProfinite
import GroupApproximation.Higman.ProfiniteBenignFactorizationReflection
import GroupApproximation.Higman.ProfiniteCofinalClosedImage
import GroupApproximation.Higman.TransportStarProdBotProfinite

/-!
# The closed semantic base of the special TransportStar join

This file isolates the part of the special benign-join closure argument that
does not use a two-stage finite-cover theorem.  For the TransportStar source
the join with the split first factor is literally

`top.prod ((Star.coordSub T).map Star.evalHom)`.

Thus closedness of the transported output proves closedness of the source
join.  The diagonal embedding into the product of the two benign ambients is
cofinal and has closed range, so the same source join remains closed after it
is transported to `joinZ₁`, the base subgroup used by the first pinch stage.

The remaining theorem after this file is deliberately narrower: preserve
nonmembership through the two central-HNN stages.  It cannot be replaced by
residual finiteness of the join ambient alone.
-/

namespace GroupApproximation
namespace Higman
namespace TransportStarSpecialJoinClosed

noncomputable section

open Conj
open scoped Pointwise

variable {G : Type} [Group G] {A₁ A₂ : Subgroup G}

/-- Elementwise form of profinite closedness, used when the element already
lies outside a split HNN base. -/
theorem exists_finite_separating_of_closed {H : Subgroup G}
    (hclosed : profiniteClosure H = H) {x : G} (hx : x ∉ H) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (q : G →* Q),
      q x ∉ H.map q := by
  classical
  by_contra h
  apply hx
  rw [← hclosed]
  intro Q _ _ q
  by_contra hq
  exact h ⟨Q, inferInstance, inferInstance, q, hq⟩

/-- Product separation for the first pinch stage is exactly product
separation of the first witness.  The second coordinate of `joinM₁` is
unrestricted, so the detector is obtained by projecting to the first
ambient. -/
theorem joinQ₁_mul_joinM₁
    (u₁ : ProfiniteBenignWitness A₁)
    (u₂ : ProfiniteBenignWitness A₂)
    (hu₁ : u₁.ProductSeparable) :
    SetProductSeparable
      (Higman.joinQ₁ u₁.witness u₂.witness)
      (Higman.joinM₁ u₁.witness u₂.witness) := by
  intro x hx
  have hx₁ : x.1 ∉
      (u₁.witness.emb.range : Set u₁.witness.K) *
        (u₁.witness.L : Set u₁.witness.K) := by
    intro hmem
    obtain ⟨a, ⟨g, rfl⟩, l, hl, hal⟩ := hmem
    apply hx
    refine ⟨Higman.joinEmb u₁.witness u₂.witness g, ?_,
      (l, (u₂.witness.emb g)⁻¹ * x.2), ?_, ?_⟩
    · exact ⟨g, Subgroup.mem_top g, rfl⟩
    · exact Subgroup.mem_prod.mpr ⟨hl, Subgroup.mem_top _⟩
    · apply Prod.ext
      · exact hal
      · exact mul_inv_cancel_left _ _
  obtain ⟨Q, hQgroup, hQfinite, q, hq⟩ := hu₁ x.1 hx₁
  refine ⟨Q, hQgroup, hQfinite,
    q.comp (MonoidHom.fst u₁.witness.K u₂.witness.K), ?_⟩
  intro hmem
  obtain ⟨a, ha, l, hl, hal⟩ := hmem
  obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.mp hl
  obtain ⟨g, -, rfl⟩ := ha₀
  have hl₁ : l₀.1 ∈ u₁.witness.L := (Subgroup.mem_prod.mp hl₀).1
  apply hq
  refine ⟨q (u₁.witness.emb g),
    ⟨u₁.witness.emb g, ⟨g, rfl⟩, rfl⟩,
    q l₀.1, ⟨l₀.1, hl₁, rfl⟩, ?_⟩
  exact hal

/-- The other first-stage vertex product is separable once the first witness
reflects source--cutter collisions in prescribed finite quotients.  This is
the precise extra invariant needed in addition to `ProductSeparable`: the
closed source join detects the source coefficient, while reflection prevents
the ambient cutter from creating a false factorization after passage to the
chosen finite quotient. -/
theorem joinZ₁_mul_joinM₁
    (u₁ : ProfiniteBenignWitness A₁)
    (u₂ : ProfiniteBenignWitness A₂)
    (hu₁ : u₁.ProductSeparable)
    (hreflect : u₁.FactorizationReflecting)
    (hsource : profiniteClosure (A₁ ⊔ A₂) = A₁ ⊔ A₂) :
    SetProductSeparable
      (Higman.joinZ₁ u₁.witness u₂.witness)
      (Higman.joinM₁ u₁.witness u₂.witness) := by
  intro x hx
  by_cases hxQ : x ∈
      (Higman.joinQ₁ u₁.witness u₂.witness :
        Set (Higman.JoinBase u₁.witness u₂.witness)) *
      (Higman.joinM₁ u₁.witness u₂.witness :
        Set (Higman.JoinBase u₁.witness u₂.witness))
  · obtain ⟨a, ha, l₀, hl₀, hax⟩ := hxQ
    obtain ⟨g, -, rfl⟩ := ha
    have hg : g ∉ A₁ ⊔ A₂ := by
      intro hg
      apply hx
      refine ⟨Higman.joinEmb u₁.witness u₂.witness g, ?_, l₀,
        hl₀, hax⟩
      exact ⟨g, hg, rfl⟩
    obtain ⟨Q, hQgroup, hQfinite, q, hq⟩ :=
      exists_finite_separating_of_closed hsource hg
    letI : Group Q := hQgroup
    letI : Finite Q := hQfinite
    obtain ⟨R, hRgroup, hRfinite, p₁, hp₁⟩ := hreflect Q q
    let p : Higman.JoinBase u₁.witness u₂.witness →* R :=
      p₁.comp (MonoidHom.fst u₁.witness.K u₂.witness.K)
    refine ⟨R, hRgroup, hRfinite, p, ?_⟩
    intro hmem
    obtain ⟨z, hz, l, hl, hzl⟩ := hmem
    obtain ⟨z₀, hz₀, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨l₁, hl₁, rfl⟩ := Subgroup.mem_map.mp hl
    obtain ⟨j, hj, rfl⟩ := hz₀
    have hl₁₁ : l₁.1 ∈ u₁.witness.L :=
      (Subgroup.mem_prod.mp hl₁).1
    have hl₀₁ : l₀.1 ∈ u₁.witness.L :=
      (Subgroup.mem_prod.mp hl₀).1
    have hcollision :
        p₁ (u₁.witness.emb (j⁻¹ * g)) ∈ u₁.witness.L.map p₁ := by
      refine ⟨l₁.1 * l₀.1⁻¹,
        u₁.witness.L.mul_mem hl₁₁
          (u₁.witness.L.inv_mem hl₀₁), ?_⟩
      have haxp := congrArg p hax
      rw [map_mul] at haxp
      have heq := hzl.trans haxp.symm
      change p₁ (u₁.witness.emb j) * p₁ l₁.1 =
        p₁ (u₁.witness.emb g) * p₁ l₀.1 at heq
      rw [map_mul, map_inv, map_mul, map_inv]
      calc
        p₁ l₁.1 * (p₁ l₀.1)⁻¹ =
            (p₁ (u₁.witness.emb j))⁻¹ *
              (p₁ (u₁.witness.emb j) * p₁ l₁.1) *
                (p₁ l₀.1)⁻¹ := by group
        _ = (p₁ (u₁.witness.emb j))⁻¹ *
              (p₁ (u₁.witness.emb g) * p₁ l₀.1) *
                (p₁ l₀.1)⁻¹ := by rw [heq]
        _ = (p₁ (u₁.witness.emb j))⁻¹ *
              p₁ (u₁.witness.emb g) := by group
        _ = p₁ ((u₁.witness.emb j)⁻¹ *
              u₁.witness.emb g) := by rw [map_mul, map_inv]
    obtain ⟨a, haA, haeq⟩ := hp₁ (j⁻¹ * g) hcollision
    apply hq
    refine ⟨j * a, ?_, ?_⟩
    · exact (A₁ ⊔ A₂).mul_mem
        hj (Subgroup.mem_sup_left haA)
    · rw [map_mul, haeq, map_mul, map_inv]
      group
  · obtain ⟨Q, hQgroup, hQfinite, q, hq⟩ :=
      joinQ₁_mul_joinM₁ u₁ u₂ hu₁ x hxQ
    refine ⟨Q, hQgroup, hQfinite, q, ?_⟩
    intro hmem
    apply hq
    obtain ⟨z, hz, l, hl, hzl⟩ := hmem
    refine ⟨z, ?_, l, hl, hzl⟩
    obtain ⟨z₀, hz₀, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨g, -, rfl⟩ := hz₀
    exact ⟨Higman.joinEmb u₁.witness u₂.witness g,
      ⟨g, Subgroup.mem_top g, rfl⟩, rfl⟩

/-- At the second pinch stage, product separation is inherited from the
second witness.  An element outside the first HNN base is separated from the
whole base using its split retraction; an element in the base is detected on
the second product coordinate. -/
theorem joinQ₂_mul_joinM₂
    (u₁ : ProfiniteBenignWitness A₁)
    (u₂ : ProfiniteBenignWitness A₂)
    (hu₂ : u₂.ProductSeparable) :
    SetProductSeparable
      (Higman.joinQ₂ u₁.witness u₂.witness)
      (Higman.joinM₂' u₁.witness u₂.witness) := by
  letI : Group.ResiduallyFinite u₁.witness.K := u₁.ambientRF
  letI : Group.ResiduallyFinite u₂.witness.K := u₂.ambientRF
  letI : Group.ResiduallyFinite
      (Higman.JoinLevel1 u₁.witness u₂.witness) :=
    BenignJoinResiduallyFinite.level1_residuallyFinite
      u₁.witness u₂.witness u₁.cutterClosed
  intro x hx
  by_cases hxbase : x ∈
      (HNNExtension.of :
        Higman.JoinBase u₁.witness u₂.witness →*
          Higman.JoinLevel1 u₁.witness u₂.witness).range
  · obtain ⟨y, rfl⟩ := hxbase
    have hy₂ : y.2 ∉
        (u₂.witness.emb.range : Set u₂.witness.K) *
          (u₂.witness.L : Set u₂.witness.K) := by
      intro hmem
      obtain ⟨a, ⟨g, rfl⟩, l, hl, hal⟩ := hmem
      apply hx
      refine ⟨HNNExtension.of
          (Higman.joinEmb u₁.witness u₂.witness g), ?_,
        HNNExtension.of
          ((u₁.witness.emb g)⁻¹ * y.1, l), ?_, ?_⟩
      · exact ⟨g, Subgroup.mem_top g, rfl⟩
      · refine ⟨((u₁.witness.emb g)⁻¹ * y.1, l), ?_, rfl⟩
        exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, hl⟩
      · change HNNExtension.of
            (Higman.joinEmb u₁.witness u₂.witness g) *
            HNNExtension.of ((u₁.witness.emb g)⁻¹ * y.1, l) =
          HNNExtension.of y
        rw [← map_mul]
        congr 1
        apply Prod.ext
        · exact mul_inv_cancel_left _ _
        · exact hal
    obtain ⟨Q, hQgroup, hQfinite, q, hq⟩ := hu₂ y.2 hy₂
    let r := CentralHNNFreeLabel.baseRet
      (Higman.joinM₁ u₁.witness u₂.witness)
    let p : Higman.JoinLevel1 u₁.witness u₂.witness →* Q :=
      (q.comp (MonoidHom.snd u₁.witness.K u₂.witness.K)).comp r
    refine ⟨Q, hQgroup, hQfinite, p, ?_⟩
    intro hmem
    obtain ⟨a, ha, l, hl, hal⟩ := hmem
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.mp hl
    obtain ⟨g, -, rfl⟩ := ha₀
    obtain ⟨l₁, hl₁, rfl⟩ := hl₀
    have hl₂ : l₁.2 ∈ u₂.witness.L :=
      (Subgroup.mem_prod.mp hl₁).2
    apply hq
    refine ⟨q (u₂.witness.emb g),
      ⟨u₂.witness.emb g, ⟨g, rfl⟩, rfl⟩,
      q l₁.2, ⟨l₁.2, hl₂, rfl⟩, ?_⟩
    exact hal
  · have hbaseClosed : profiniteClosure
        (HNNExtension.of :
          Higman.JoinBase u₁.witness u₂.witness →*
            Higman.JoinLevel1 u₁.witness u₂.witness).range =
        (HNNExtension.of :
          Higman.JoinBase u₁.witness u₂.witness →*
            Higman.JoinLevel1 u₁.witness u₂.witness).range := by
      exact profiniteClosure_range_eq_range_of_retraction
        (HNNExtension.of :
          Higman.JoinBase u₁.witness u₂.witness →*
            Higman.JoinLevel1 u₁.witness u₂.witness)
        (CentralHNNFreeLabel.baseRet
          (Higman.joinM₁ u₁.witness u₂.witness))
        (BenignJoinResiduallyFinite.baseRet_comp_of
          u₁.witness u₂.witness
          (Higman.joinM₁ u₁.witness u₂.witness))
    obtain ⟨Q, hQgroup, hQfinite, q, hq⟩ :=
      exists_finite_separating_of_closed
        (G := Higman.JoinLevel1 u₁.witness u₂.witness)
        hbaseClosed hxbase
    refine ⟨Q, hQgroup, hQfinite, q, ?_⟩
    intro hmem
    apply hq
    obtain ⟨a, ha, l, hl, hal⟩ := hmem
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.mp hl
    obtain ⟨g, -, rfl⟩ := ha₀
    obtain ⟨l₁, -, rfl⟩ := hl₀
    refine ⟨HNNExtension.of
      (Higman.joinEmb u₁.witness u₂.witness g * l₁),
      ⟨Higman.joinEmb u₁.witness u₂.witness g * l₁, rfl⟩, ?_⟩
    rw [map_mul, map_mul]
    exact hal

/-- The semantic TransportStar join is closed before either HNN letter is
adjoined. -/
theorem sourceJoin
    (T : Set ↑K)
    (hout : profiniteClosure ((Star.coordSub T).map Star.evalHom) =
      (Star.coordSub T).map Star.evalHom) :
    profiniteClosure
        ((Star.graphSub ⊓
            ((Star.coordSub T).map cbHom).comap
              (MonoidHom.fst F₃ F₃)) ⊔ Star.ProdBot) =
      (Star.graphSub ⊓
          ((Star.coordSub T).map cbHom).comap
            (MonoidHom.fst F₃ F₃)) ⊔ Star.ProdBot :=
  Star.special_sup_closed_of_eval_closed T hout

/-- The closed semantic join remains closed in the product base of the two
benign witnesses.  This is the exact closed `Z` input for the first
finite-cover pinch stage. -/
theorem joinZ₁
    (T : Set ↑K)
    (u : ProfiniteBenignWitness
      (Star.graphSub ⊓
        ((Star.coordSub T).map cbHom).comap
          (MonoidHom.fst F₃ F₃)))
    (hout : profiniteClosure ((Star.coordSub T).map Star.evalHom) =
      (Star.coordSub T).map Star.evalHom) :
    profiniteClosure
        (Higman.joinZ₁ u.witness Star.prodBotWitness.witness) =
      Higman.joinZ₁ u.witness Star.prodBotWitness.witness := by
  exact profiniteClosure_joinZ₁_of_source_closed
    u Star.prodBotWitness (sourceJoin T hout)

/-- Concrete TransportStar specialization of the first-stage `Z * M`
separation theorem. -/
theorem firstVertexProduct
    (T : Set ↑K)
    (u : ProfiniteBenignWitness
      (Star.graphSub ⊓
        ((Star.coordSub T).map cbHom).comap
          (MonoidHom.fst F₃ F₃)))
    (hu : u.ProductSeparable)
    (hreflect : u.FactorizationReflecting)
    (hout : profiniteClosure ((Star.coordSub T).map Star.evalHom) =
      (Star.coordSub T).map Star.evalHom) :
    SetProductSeparable
      (Higman.joinZ₁ u.witness Star.prodBotWitness.witness)
      (Higman.joinM₁ u.witness Star.prodBotWitness.witness) :=
  joinZ₁_mul_joinM₁ u Star.prodBotWitness hu hreflect
    (sourceJoin T hout)

end

end TransportStarSpecialJoinClosed
end Higman
end GroupApproximation
