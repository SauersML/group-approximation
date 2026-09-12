import GroupApproximation.GroupTheory.FiniteHNNResiduallyFinite
import GroupApproximation.Algebra.HNNSubextension
import GroupApproximation.Sofic.ProfiniteClosure

/-!
# Residual finiteness of central HNN extensions over separable subgroups

If `G` is residually finite and `M ≤ G` is profinitely closed, then the
central HNN extension which adjoins a stable letter commuting with `M` is
residually finite.  For a fixed Britton-reduced word, closedness supplies one
finite quotient of the base which keeps every potentially pinching syllable
outside the image of `M`.  The word therefore remains Britton reduced in the
HNN extension of the finite quotient.  Residual finiteness of finite-base HNN
extensions finishes the separation.
-/

namespace GroupApproximation
namespace CentralHNNResiduallyFinite

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- A point outside a profinitely closed subgroup is separated from that
subgroup in one finite quotient. -/
theorem exists_finite_quotient_not_mem_of_closed (M : Subgroup G)
    (hM : profiniteClosure M = M) {x : G} (hx : x ∉ M) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (q : G →* Q),
      q x ∉ M.map q := by
  by_contra hnone
  have hall : ∀ (Q : Type) [Group Q] [Finite Q] (q : G →* Q),
      q x ∈ M.map q := by
    intro Q _ _ q
    by_contra hq
    exact hnone ⟨Q, inferInstance, inferInstance, q, hq⟩
  have hxcl : x ∈ profiniteClosure M := hall
  rw [hM] at hxcl
  exact hx hxcl

/-- Projecting a product quotient preserves every separation supplied by its
first coordinate. -/
theorem not_mem_map_prod_left {Q R : Type} [Group Q] [Group R]
    (M : Subgroup G) (q : G →* Q) (r : G →* R) {x : G}
    (hx : q x ∉ M.map q) : (q.prod r) x ∉ M.map (q.prod r) := by
  intro h
  obtain ⟨m, hm, hmx⟩ := h
  apply hx
  refine ⟨m, hm, ?_⟩
  exact congrArg Prod.fst hmx

/-- Projecting a product quotient preserves every separation supplied by its
second coordinate. -/
theorem not_mem_map_prod_right {Q R : Type} [Group Q] [Group R]
    (M : Subgroup G) (q : G →* Q) (r : G →* R) {x : G}
    (hx : r x ∉ M.map r) : (q.prod r) x ∉ M.map (q.prod r) := by
  intro h
  obtain ⟨m, hm, hmx⟩ := h
  apply hx
  refine ⟨m, hm, ?_⟩
  exact congrArg Prod.snd hmx

/-- One finite quotient simultaneously preserves all non-memberships appearing
in a finite syllable list. -/
theorem exists_finite_quotient_separating_list (M : Subgroup G)
    (hM : profiniteClosure M = M) :
    ∀ l : List (ℤˣ × G),
      ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (q : G →* Q),
        ∀ p ∈ l, p.2 ∉ M → q p.2 ∉ M.map q
  | [] => by
      refine ⟨PUnit, inferInstance, inferInstance, 1, ?_⟩
      simp
  | p :: l => by
      obtain ⟨Q, hQgroup, hQfinite, q, hq⟩ :=
        exists_finite_quotient_separating_list M hM l
      letI : Group Q := hQgroup
      letI : Finite Q := hQfinite
      by_cases hp : p.2 ∈ M
      · refine ⟨Q, inferInstance, inferInstance, q, ?_⟩
        intro z hz hzM
        by_cases hzp : z = p
        · subst z
          exact absurd hp hzM
        · have hz' : z ∈ l := by simpa [hzp] using hz
          exact hq z hz' hzM
      · obtain ⟨R, hRgroup, hRfinite, r, hr⟩ :=
          exists_finite_quotient_not_mem_of_closed M hM hp
        letI : Group R := hRgroup
        letI : Finite R := hRfinite
        refine ⟨Q × R, inferInstance, inferInstance, q.prod r, ?_⟩
        intro z hz hzM
        by_cases hzp : z = p
        · subst z
          exact not_mem_map_prod_right M q r hr
        · have hz' : z ∈ l := by simpa [hzp] using hz
          exact not_mem_map_prod_left M q r (hq z hz' hzM)

/-- Mapping a Britton-reduced central-HNN spelling through a quotient remains
Britton reduced when all its non-edge syllables stay outside the edge image. -/
theorem noPinch_mapList_of_separates {Q : Type} [Group Q]
    (M : Subgroup G) (q : G →* Q) :
    ∀ (l : List (ℤˣ × G)),
      HNNBritton.NoPinch M M l →
      (∀ p ∈ l, p.2 ∉ M → q p.2 ∉ M.map q) →
      HNNBritton.NoPinch (M.map q) (M.map q) (HNNSubextension.mapList q l)
  | [], _, _ => HNNBritton.noPinch_nil
  | [_], _, _ => HNNBritton.noPinch_singleton _
  | x :: y :: l, hred, hsep => by
      rw [HNNSubextension.mapList_cons, HNNSubextension.mapList_cons]
      refine HNNBritton.noPinch_cons_cons ?_
        (noPinch_mapList_of_separates M q (y :: l) hred.tail ?_)
      · intro hmem
        by_contra hsign
        have hxM : x.2 ∉ M := by
          intro hxM
          have hto : HNNExtension.toSubgroup M M x.1 = M := by
            rcases Int.units_eq_one_or x.1 with hx | hx
            · rw [hx, HNNExtension.toSubgroup_one]
            · rw [hx, HNNExtension.toSubgroup_neg_one]
          exact hsign (hred.seam y (by simp) (by rwa [hto]))
        have hto : HNNExtension.toSubgroup (M.map q) (M.map q) x.1 =
            M.map q := by
          rcases Int.units_eq_one_or x.1 with hx | hx
          · rw [hx, HNNExtension.toSubgroup_one]
          · rw [hx, HNNExtension.toSubgroup_neg_one]
        exact hsep x (by simp) hxM (by rwa [← hto])
      · intro p hp
        exact hsep p (by simp [hp])

/-- The homomorphism induced by a quotient of the base, fixing the central
stable letter. -/
def mapCentral {Q : Type} [Group Q] (M : Subgroup G) (q : G →* Q) :
    HNNExtension G M M (MulEquiv.refl M) →*
      HNNExtension Q (M.map q) (M.map q) (MulEquiv.refl (M.map q)) :=
  HNNExtension.lift
    ((HNNExtension.of : Q →*
      HNNExtension Q (M.map q) (M.map q) (MulEquiv.refl (M.map q))).comp q)
    HNNExtension.t (by
      intro a
      have ha : q (a : G) ∈ M.map q := ⟨a, a.2, rfl⟩
      have hconj := HNNExtension.equiv_eq_conj
        (φ := MulEquiv.refl (M.map q)) ⟨q (a : G), ha⟩
      have hgoal :
          HNNExtension.of (q (a : G)) =
            (HNNExtension.t : HNNExtension Q (M.map q) (M.map q)
              (MulEquiv.refl (M.map q))) * HNNExtension.of (q (a : G)) *
                HNNExtension.t⁻¹ := by simpa using hconj
      exact mul_inv_eq_iff_eq_mul.mp hgoal.symm)

@[simp] theorem mapCentral_of {Q : Type} [Group Q]
    (M : Subgroup G) (q : G →* Q) (g : G) :
    mapCentral M q (HNNExtension.of g) = HNNExtension.of (q g) := by
  simp [mapCentral, HNNExtension.lift_of]

@[simp] theorem mapCentral_t {Q : Type} [Group Q]
    (M : Subgroup G) (q : G →* Q) :
    mapCentral M q
      (HNNExtension.t : HNNExtension G M M (MulEquiv.refl M)) =
        (HNNExtension.t :
          HNNExtension Q (M.map q) (M.map q) (MulEquiv.refl (M.map q))) := by
  simp [mapCentral, HNNExtension.lift_t]

/-- `mapCentral` carries a spelling to the coefficientwise mapped spelling. -/
theorem mapCentral_wordProd {Q : Type} [Group Q]
    (M : Subgroup G) (q : G →* Q) (g : G) (l : List (ℤˣ × G)) :
    mapCentral M q (HNNBritton.wordProd (MulEquiv.refl M) g l) =
      HNNBritton.wordProd (MulEquiv.refl (M.map q)) (q g)
        (HNNSubextension.mapList q l) := by
  apply HNNSubextension.map_wordProd
  exact
    { map_of := mapCentral_of M q
      map_t := mapCentral_t M q }

/-- A central HNN extension of a residually finite group over a profinitely
closed subgroup is residually finite. -/
theorem centralHNN_residuallyFinite [Group.ResiduallyFinite G]
    (M : Subgroup G) (hM : profiniteClosure M = M) :
    Group.ResiduallyFinite
      (HNNExtension G M M (MulEquiv.refl M)) := by
  classical
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro z hz
  obtain ⟨g, l, hred, hword⟩ :=
    HNNBritton.exists_hasSpelling (MulEquiv.refl M) z
  by_cases hnil : l = []
  · subst l
    have hg : g ≠ 1 := by
      intro hg
      subst g
      apply hz
      simpa using hword.symm
    obtain ⟨N, hN⟩ := Group.exists_finiteIndexNormalSubgroup_notMem g hg
    letI := N.isNormal'
    letI := N.isFiniteIndex'
    let Q := G ⧸ N.toSubgroup
    haveI : Finite Q := Subgroup.finite_quotient_of_finiteIndex
    let q : G →* Q := QuotientGroup.mk' N.toSubgroup
    let collapse : HNNExtension G M M (MulEquiv.refl M) →* Q :=
      HNNExtension.lift q 1 (by intro a; simp)
    refine ⟨Q, inferInstance, inferInstance, collapse, ?_⟩
    intro hcollapse
    apply hN
    have hqg : q g = 1 := by
      rw [← hword] at hcollapse
      simpa [collapse, HNNBritton.wordProd_nil,
        HNNExtension.lift_of] using hcollapse
    exact (QuotientGroup.eq_one_iff g).mp hqg
  · obtain ⟨Q, hQgroup, hQfinite, q, hsep⟩ :=
      exists_finite_quotient_separating_list M hM l
    letI : Group Q := hQgroup
    letI : Finite Q := hQfinite
    letI : Fintype Q := Fintype.ofFinite Q
    let MQ : Subgroup Q := M.map q
    let E := HNNExtension Q MQ MQ (MulEquiv.refl MQ)
    let Ψ : HNNExtension G M M (MulEquiv.refl M) →* E := mapCentral M q
    have hmapred :
        HNNBritton.NoPinch MQ MQ (HNNSubextension.mapList q l) :=
      noPinch_mapList_of_separates M q l hred hsep
    have hmapnil : HNNSubextension.mapList q l ≠ [] :=
      HNNSubextension.mapList_ne_nil q hnil
    have hΨz : Ψ z ≠ 1 := by
      rw [← hword]
      rw [mapCentral_wordProd]
      exact HNNBritton.wordProd_ne_one (MulEquiv.refl MQ) hmapnil hmapred
    letI : Group.ResiduallyFinite E :=
      FiniteHNNFreeLabelAction.finiteBaseHNN_residuallyFinite
        (phi := MulEquiv.refl MQ)
    obtain ⟨N, hN⟩ := Group.exists_finiteIndexNormalSubgroup_notMem (Ψ z) hΨz
    letI := N.isNormal'
    letI := N.isFiniteIndex'
    let R := E ⧸ N.toSubgroup
    haveI : Finite R := Subgroup.finite_quotient_of_finiteIndex
    let r : E →* R := QuotientGroup.mk' N.toSubgroup
    let liftR : R →* ULift.{u} R :=
      (MulEquiv.ulift (α := R)).symm.toMonoidHom
    refine ⟨ULift.{u} R, inferInstance, inferInstance,
      liftR.comp (r.comp Ψ), ?_⟩
    intro hr
    apply hN
    have hr' : r (Ψ z) = 1 := by
      have := congrArg (MulEquiv.ulift (α := R)) hr
      simpa [liftR] using this
    exact (QuotientGroup.eq_one_iff (Ψ z)).mp hr'

end

end CentralHNNResiduallyFinite
end GroupApproximation
