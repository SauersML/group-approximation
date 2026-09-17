import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ContactMapHolds
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces.ComponentClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# Holding small faces of the contact map: the charge

Write `M` for the dual of the diagram, `N = contactMap P` and `K_x = CK P x` for the ambient darts
of the component of `x` in `N`.  The full proof is in the docstring of `FaceClassTools`.

* `IsOuter P F`: some `x ∈ F` and `y` at the exterior have `x ∼_{K_x} y`, and the vertex orbit
  of `y` carries no dart of `K_x`.
* `HoldsVia P F o`: `HoldsObject P F` with the object `o` exposed.
* `not_ck_of_holds`: a face holding `o` sees no dart of its component at `o`.
* `holds_inj`: two non-outer faces holding one object coincide.  Inside one component this is
  separation; across components `false_of_not_componentOf` makes one of them outer.
* `outer_inj`: two outer faces with a common object vertex coincide.
* `card_inner_le`, `card_outer_le`: each kind numbers at most `n + 1`.

## Manuscript status

Infrastructure for `thm:hull` (through the contact count of Osin's Lemma 9.4,
arXiv:math/0411039v3, §9); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open scoped Classical

/-- Darts at one face of a map lie at one vertex of its dual. -/
theorem dual_sameCycle_of_faceOf_eq (M : CombMap.{u}) {a b : M.Dart}
    (h : M.faceOf a = M.faceOf b) : M.dual.sigma.SameCycle a b :=
  (M.faceOf_eq_iff a b).mp h

/-- Darts at one vertex of the dual lie at one face of the map. -/
theorem faceOf_eq_of_dual_sameCycle (M : CombMap.{u}) {a b : M.dual.Dart}
    (h : M.dual.sigma.SameCycle a b) : M.faceOf a = M.faceOf b :=
  (M.faceOf_eq_iff a b).mpr h

section Charge

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- The ambient darts of the component of a contact dart. -/
abbrev CK (P : OsinLemma94RealizedPolygons S) (x : P.contactMap.Dart) :
    S.diagram.toCombMap.dual.Dart → Prop :=
  CompKeep (M := S.diagram.toCombMap.dual) (keep := P.ContactKeep) P.contactKeep_alpha x

theorem ck_keep (P : OsinLemma94RealizedPolygons S) {x : P.contactMap.Dart}
    {z : S.diagram.toCombMap.dual.Dart} (h : CK P x z) : P.ContactKeep z :=
  keep_of_compKeep (M := S.diagram.toCombMap.dual) (keep := P.ContactKeep) P.contactKeep_alpha h

theorem ck_alpha (P : OsinLemma94RealizedPolygons S) (x : P.contactMap.Dart)
    (z : S.diagram.toCombMap.dual.Dart) :
    CK P x (S.diagram.toCombMap.dual.alpha z) ↔ CK P x z :=
  compKeep_alpha (M := S.diagram.toCombMap.dual) (keep := P.ContactKeep) P.contactKeep_alpha x z

theorem ck_self (P : OsinLemma94RealizedPolygons S) (x : P.contactMap.Dart) : CK P x x.1 :=
  compKeep_self (M := S.diagram.toCombMap.dual) (keep := P.ContactKeep) P.contactKeep_alpha x

theorem ck_congr (P : OsinLemma94RealizedPolygons S) {x x' : P.contactMap.Dart}
    (h : P.contactMap.componentOf x x') (z : S.diagram.toCombMap.dual.Dart) :
    CK P x z ↔ CK P x' z :=
  compKeep_congr (M := S.diagram.toCombMap.dual) (keep := P.ContactKeep) P.contactKeep_alpha h z

/-- A face class off the retained edges is a face class off a component. -/
theorem ck_of_keep (P : OsinLemma94RealizedPolygons S) (x : P.contactMap.Dart)
    {a b : S.diagram.toCombMap.dual.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep S.diagram.toCombMap.dual P.ContactKeep) a b) :
    Relation.EqvGen (CombMap.FaceClassStep S.diagram.toCombMap.dual (CK P x)) a b :=
  faceClass_mono (M := S.diagram.toCombMap.dual) (K := P.ContactKeep) (K' := CK P x)
    (fun _ hz => ck_keep P hz) h

/-- Separation inside a component of the contact map. -/
theorem separation (P : OsinLemma94RealizedPolygons S) {d d' : P.contactMap.Dart}
    (hcomp : P.contactMap.componentOf d d')
    (hp : Relation.EqvGen (CombMap.FaceClassStep S.diagram.toCombMap.dual (CK P d)) d.1 d'.1) :
    P.contactMap.faceOf d = P.contactMap.faceOf d' :=
  faceOf_eq_of_compKeep (M := S.diagram.toCombMap.dual) (keep := P.ContactKeep)
    P.contactKeep_alpha (OsinLemma94RealizedPolygons.dual_planar_diagram S) hcomp hp

theorem avoid (P : OsinLemma94RealizedPolygons S) {x₁ x₂ : P.contactMap.Dart}
    (h12 : ¬ P.contactMap.componentOf x₁ x₂) {w : P.contactMap.Dart}
    (hw : P.contactMap.componentOf x₁ w) {z : S.diagram.toCombMap.dual.Dart}
    (hz : S.diagram.toCombMap.dual.sigma.SameCycle w.1 z) : ¬ CK P x₂ z :=
  not_compKeep_of_componentOf (M := S.diagram.toCombMap.dual) (keep := P.ContactKeep)
    P.contactKeep_alpha h12 hw hz

/-- The darts of the component of `x₁` lie in one face class off the component of `x₂`. -/
theorem block (P : OsinLemma94RealizedPolygons S) {x₁ x₂ : P.contactMap.Dart}
    (h12 : ¬ P.contactMap.componentOf x₁ x₂) {w : P.contactMap.Dart}
    (hw : P.contactMap.componentOf x₁ w) :
    Relation.EqvGen (CombMap.FaceClassStep S.diagram.toCombMap.dual (CK P x₂)) x₁.1 w.1 :=
  faceClass_of_componentOf (M := S.diagram.toCombMap.dual) (keep := P.ContactKeep)
    P.contactKeep_alpha (K := CK P x₂) x₁ (fun _ hw' _ hz => avoid P h12 hw' hz) hw

theorem comp_of_sameCycle (P : OsinLemma94RealizedPolygons S) {a b : P.contactMap.Dart}
    (h : S.diagram.toCombMap.dual.sigma.SameCycle a.1 b.1) : P.contactMap.componentOf a b :=
  componentOf_of_ambient_sameCycle (M := S.diagram.toCombMap.dual) (keep := P.ContactKeep)
    P.contactKeep_alpha h

/-- **An outer face**: a dart of it reaches the exterior through a vertex free of its component. -/
def IsOuter (P : OsinLemma94RealizedPolygons S) (F : P.contactMap.Face) : Prop :=
  ∃ x : P.contactMap.Dart, P.contactMap.faceOf x = F ∧
    ∃ y : S.diagram.toCombMap.dual.Dart,
      S.diagram.toCombMap.faceOf y = OsinLemma94RealizedPolygons.objectFace S none ∧
        (∀ z, S.diagram.toCombMap.dual.sigma.SameCycle y z → ¬ CK P x z) ∧
          Relation.EqvGen (CombMap.FaceClassStep S.diagram.toCombMap.dual (CK P x)) x.1 y

/-- `HoldsObject` with its object exposed. -/
def HoldsVia (P : OsinLemma94RealizedPolygons S) (F : P.contactMap.Face)
    (o : Option (Fin S.diagram.rCellCount)) : Prop :=
  ∃ x : P.contactMap.Dart, P.contactMap.faceOf x = F ∧
    ∃ y : S.diagram.toCombMap.dual.Dart,
      Relation.EqvGen (CombMap.FaceClassStep S.diagram.toCombMap.dual P.ContactKeep) x.1 y ∧
        S.diagram.toCombMap.faceOf y = OsinLemma94RealizedPolygons.objectFace S o ∧
          ∀ z : P.contactMap.Dart, P.contactMap.faceOf z = F →
            S.diagram.toCombMap.faceOf z.1 ≠ OsinLemma94RealizedPolygons.objectFace S o

theorem holdsVia_of_holdsObject (P : OsinLemma94RealizedPolygons S) {F : P.contactMap.Face}
    (h : P.HoldsObject F) : ∃ o, HoldsVia P F o := by
  obtain ⟨x, hx, y, hxy, o, hyo, hno⟩ := h
  exact ⟨o, x, hx, y, hxy, hyo, hno⟩

/-- **A holding face sees no dart of its component at the held object.** -/
theorem not_ck_of_holds (P : OsinLemma94RealizedPolygons S) {x : P.contactMap.Dart}
    {y : S.diagram.toCombMap.dual.Dart} {o : Option (Fin S.diagram.rCellCount)}
    (hxy : Relation.EqvGen (CombMap.FaceClassStep S.diagram.toCombMap.dual P.ContactKeep) x.1 y)
    (hyo : S.diagram.toCombMap.faceOf y = OsinLemma94RealizedPolygons.objectFace S o)
    (hno : ∀ z : P.contactMap.Dart, P.contactMap.faceOf z = P.contactMap.faceOf x →
      S.diagram.toCombMap.faceOf z.1 ≠ OsinLemma94RealizedPolygons.objectFace S o)
    (z : S.diagram.toCombMap.dual.Dart) (hyz : S.diagram.toCombMap.dual.sigma.SameCycle y z) :
    ¬ CK P x z := by
  intro hz
  obtain ⟨z', ⟨hk, hc⟩, hyz', hpath⟩ :=
    exists_keep_faceClass (M := S.diagram.toCombMap.dual) (K := CK P x) hyz hz
  have hface : P.contactMap.faceOf x = P.contactMap.faceOf ⟨z', hk⟩ :=
    separation P hc (Relation.EqvGen.trans _ _ _ (ck_of_keep P x hxy) hpath)
  exact hno ⟨z', hk⟩ hface.symm
    ((faceOf_eq_of_dual_sameCycle S.diagram.toCombMap hyz').symm.trans hyo)

/-- A face whose component reaches the exterior only through its blocks is outer. -/
theorem isOuter_of_block (P : OsinLemma94RealizedPolygons S) {x₁ x₂ : P.contactMap.Dart}
    (h12 : ¬ P.contactMap.componentOf x₁ x₂)
    (hpath : Relation.EqvGen (CombMap.FaceClassStep S.diagram.toCombMap.dual (CK P x₂)) x₂.1 x₁.1)
    {w : P.contactMap.Dart} (hw : P.contactMap.componentOf x₁ w)
    {y : S.diagram.toCombMap.dual.Dart}
    (hyr : S.diagram.toCombMap.faceOf y = OsinLemma94RealizedPolygons.objectFace S none)
    (hav : ∀ z, S.diagram.toCombMap.dual.sigma.SameCycle y z → ¬ CK P x₂ z)
    (hyw : Relation.EqvGen (CombMap.FaceClassStep S.diagram.toCombMap.dual (CK P x₂)) y w.1) :
    IsOuter P (P.contactMap.faceOf x₂) :=
  ⟨x₂, rfl, y, hyr, hav, Relation.EqvGen.trans _ _ _ hpath
    (Relation.EqvGen.trans _ _ _ (block P h12 hw) (Relation.EqvGen.symm _ _ hyw))⟩

/-- A component that never meets the exterior has no dart at an exterior vertex. -/
theorem not_ck_of_not_exterior (P : OsinLemma94RealizedPolygons S) {x : P.contactMap.Dart}
    (hA : ¬ ∃ w : P.contactMap.Dart, P.contactMap.componentOf x w ∧
      S.diagram.toCombMap.faceOf w.1 = OsinLemma94RealizedPolygons.objectFace S none)
    {yr : S.diagram.toCombMap.dual.Dart}
    (hyr : S.diagram.toCombMap.faceOf yr = OsinLemma94RealizedPolygons.objectFace S none)
    (z : S.diagram.toCombMap.dual.Dart) (hz : S.diagram.toCombMap.dual.sigma.SameCycle yr z) :
    ¬ CK P x z := by
  rintro ⟨hk, hc⟩
  exact hA ⟨⟨z, hk⟩, hc, (faceOf_eq_of_dual_sameCycle S.diagram.toCombMap hz).symm.trans hyr⟩

/-- **Across components, one of two mutually reachable faces is outer.** -/
theorem false_of_not_componentOf (P : OsinLemma94RealizedPolygons S) {x₁ x₂ : P.contactMap.Dart}
    (h12 : ¬ P.contactMap.componentOf x₁ x₂)
    (hp₁ : Relation.EqvGen (CombMap.FaceClassStep S.diagram.toCombMap.dual (CK P x₁)) x₁.1 x₂.1)
    (hp₂ : Relation.EqvGen (CombMap.FaceClassStep S.diagram.toCombMap.dual (CK P x₂)) x₂.1 x₁.1)
    (hn₁ : ¬ IsOuter P (P.contactMap.faceOf x₁)) (hn₂ : ¬ IsOuter P (P.contactMap.faceOf x₂)) :
    False := by
  have h21 : ¬ P.contactMap.componentOf x₂ x₁ := fun h => h12 (Relation.EqvGen.symm _ _ h)
  by_cases hA₁ : ∃ w : P.contactMap.Dart, P.contactMap.componentOf x₁ w ∧
      S.diagram.toCombMap.faceOf w.1 = OsinLemma94RealizedPolygons.objectFace S none
  · obtain ⟨w, hw, hwr⟩ := hA₁
    exact hn₂ (isOuter_of_block P h12 hp₂ hw hwr (fun _ hz => avoid P h12 hw hz)
      (Relation.EqvGen.refl _))
  by_cases hA₂ : ∃ w : P.contactMap.Dart, P.contactMap.componentOf x₂ w ∧
      S.diagram.toCombMap.faceOf w.1 = OsinLemma94RealizedPolygons.objectFace S none
  · obtain ⟨w, hw, hwr⟩ := hA₂
    exact hn₁ (isOuter_of_block P h21 hp₁ hw hwr (fun _ hz => avoid P h21 hw hz)
      (Relation.EqvGen.refl _))
  obtain ⟨yr, hyr⟩ := Quotient.exists_rep (OsinLemma94RealizedPolygons.objectFace S none)
  have hyr' : S.diagram.toCombMap.faceOf yr = OsinLemma94RealizedPolygons.objectFace S none := hyr
  have hav₁ := not_ck_of_not_exterior P hA₁ hyr'
  have hav₂ := not_ck_of_not_exterior P hA₂ hyr'
  obtain ⟨wz, ⟨hk, hc⟩, hyw⟩ := exists_keep_of_connected (M := S.diagram.toCombMap.dual)
    (K := CK P x₁) (ck_alpha P x₁) (OsinLemma94RealizedPolygons.dual_planar_diagram S).1
    (ck_self P x₁) yr
  have hno : ∀ z, Relation.EqvGen (CombMap.FaceClassStep S.diagram.toCombMap.dual (CK P x₁)) yr z →
      ¬ CK P x₂ z := by
    rintro z hz ⟨hk₂, hc₂⟩
    exact hn₁ (isOuter_of_block P h21 hp₁ (w := ⟨z, hk₂⟩) hc₂ hyr' hav₁ hz)
  exact hn₂ (isOuter_of_block P h12 hp₂ (w := ⟨wz, hk⟩) hc hyr' hav₂
    (faceClass_transfer (M := S.diagram.toCombMap.dual) hno hyw (Relation.EqvGen.refl _)))

/-- **Non-outer faces holding one object coincide.** -/
theorem holds_inj (P : OsinLemma94RealizedPolygons S) {F₁ F₂ : P.contactMap.Face}
    {o : Option (Fin S.diagram.rCellCount)} (h₁ : HoldsVia P F₁ o) (h₂ : HoldsVia P F₂ o)
    (hn₁ : ¬ IsOuter P F₁) (hn₂ : ¬ IsOuter P F₂) : F₁ = F₂ := by
  obtain ⟨x₁, rfl, y₁, hxy₁, hyo₁, hno₁⟩ := h₁
  obtain ⟨x₂, rfl, y₂, hxy₂, hyo₂, hno₂⟩ := h₂
  have hy : S.diagram.toCombMap.dual.sigma.SameCycle y₁ y₂ :=
    dual_sameCycle_of_faceOf_eq S.diagram.toCombMap (hyo₁.trans hyo₂.symm)
  have hp₁ : Relation.EqvGen (CombMap.FaceClassStep S.diagram.toCombMap.dual (CK P x₁))
      x₁.1 x₂.1 :=
    Relation.EqvGen.trans _ _ _ (ck_of_keep P x₁ hxy₁) (Relation.EqvGen.trans _ _ _
      (faceClass_of_sameCycle (not_ck_of_holds P hxy₁ hyo₁ hno₁) hy)
      (Relation.EqvGen.symm _ _ (ck_of_keep P x₁ hxy₂)))
  have hp₂ : Relation.EqvGen (CombMap.FaceClassStep S.diagram.toCombMap.dual (CK P x₂))
      x₂.1 x₁.1 :=
    Relation.EqvGen.trans _ _ _ (ck_of_keep P x₂ hxy₂) (Relation.EqvGen.trans _ _ _
      (faceClass_of_sameCycle (not_ck_of_holds P hxy₂ hyo₂ hno₂) hy.symm)
      (Relation.EqvGen.symm _ _ (ck_of_keep P x₂ hxy₁)))
  by_cases hc : P.contactMap.componentOf x₁ x₂
  · exact separation P hc hp₁
  · exact (false_of_not_componentOf P hc hp₁ hp₂ hn₁ hn₂).elim

/-- Every face of the contact map has a dart at an object. -/
theorem exists_object_dart (P : OsinLemma94RealizedPolygons S) (F : P.contactMap.Face) :
    ∃ z : P.contactMap.Dart, P.contactMap.faceOf z = F ∧ P.contactColour z = false := by
  obtain ⟨d, hd⟩ := Quotient.exists_rep F
  have hd' : P.contactMap.faceOf d = F := hd
  cases hc : P.contactColour d with
  | false => exact ⟨d, hd', hc⟩
  | true =>
    refine ⟨P.contactMap.facePerm d, (P.contactMap.faceOf_facePerm d).trans hd', ?_⟩
    have e : P.contactMap.facePerm d = P.contactMap.sigma (P.contactMap.alpha d) := rfl
    rw [e, P.contactColour_sigma, P.contactColour_alpha, hc, Bool.not_true]

/-- **Outer faces with a common object vertex coincide.** -/
theorem outer_inj (P : OsinLemma94RealizedPolygons S) {F₁ F₂ : P.contactMap.Face}
    (h₁ : IsOuter P F₁) (h₂ : IsOuter P F₂) {o : Option (Fin S.diagram.rCellCount)}
    {z₁ z₂ : P.contactMap.Dart} (hz₁ : P.contactMap.faceOf z₁ = F₁)
    (hz₂ : P.contactMap.faceOf z₂ = F₂)
    (ho₁ : S.diagram.toCombMap.faceOf z₁.1 = OsinLemma94RealizedPolygons.objectFace S o)
    (ho₂ : S.diagram.toCombMap.faceOf z₂.1 = OsinLemma94RealizedPolygons.objectFace S o) :
    F₁ = F₂ := by
  obtain ⟨x₁, rfl, y₁, hyr₁, hav₁, hp₁⟩ := h₁
  obtain ⟨x₂, rfl, y₂, hyr₂, _, hp₂⟩ := h₂
  have hz : P.contactMap.componentOf z₁ z₂ :=
    comp_of_sameCycle P (dual_sameCycle_of_faceOf_eq S.diagram.toCombMap (ho₁.trans ho₂.symm))
  have hc : P.contactMap.componentOf x₁ x₂ :=
    Relation.EqvGen.trans _ _ _ (componentOf_of_faceOf_eq P.contactMap hz₁.symm)
      (Relation.EqvGen.trans _ _ _ hz (componentOf_of_faceOf_eq P.contactMap hz₂))
  have hy : S.diagram.toCombMap.dual.sigma.SameCycle y₁ y₂ :=
    dual_sameCycle_of_faceOf_eq S.diagram.toCombMap (hyr₁.trans hyr₂.symm)
  have hp₂' : Relation.EqvGen (CombMap.FaceClassStep S.diagram.toCombMap.dual (CK P x₁))
      x₂.1 y₂ :=
    faceClass_mono (M := S.diagram.toCombMap.dual) (K := CK P x₂) (K' := CK P x₁)
      (fun z hz' => (ck_congr P hc z).mp hz') hp₂
  exact separation P hc (Relation.EqvGen.trans _ _ _ hp₁
    (Relation.EqvGen.trans _ _ _ (faceClass_of_sameCycle hav₁ hy) (Relation.EqvGen.symm _ _ hp₂')))

/-- **The held non-outer faces number at most `n + 1`.** -/
theorem card_inner_le (P : OsinLemma94RealizedPolygons S) :
    (Finset.univ.filter fun F : P.contactMap.Face => P.HoldsObject F ∧ ¬ IsOuter P F).card ≤
      S.diagram.rCellCount + 1 := by
  let g : P.contactMap.Face → Option (Fin S.diagram.rCellCount) := fun F =>
    if h : ∃ o, HoldsVia P F o then Classical.choose h else none
  have hg : ∀ F, P.HoldsObject F → HoldsVia P F (g F) := by
    intro F hF
    have h := holdsVia_of_holdsObject P hF
    have hgF : g F = Classical.choose h := dif_pos h
    rw [hgF]
    exact Classical.choose_spec h
  refine (Finset.card_le_card_of_injOn g
    (fun F _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_).trans ?_
  · intro F hF F' hF' hgg
    obtain ⟨hh, hn⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hF)).2
    obtain ⟨hh', hn'⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hF')).2
    have h₂ := hg F' hh'
    rw [← hgg] at h₂
    exact holds_inj P (hg F hh) h₂ hn hn'
  · simp [Finset.card_univ, Fintype.card_option]

/-- **The outer faces number at most `n + 1`.** -/
theorem card_outer_le (P : OsinLemma94RealizedPolygons S) :
    (Finset.univ.filter fun F : P.contactMap.Face => IsOuter P F).card ≤
      S.diagram.rCellCount + 1 := by
  let g : P.contactMap.Face → Option (Fin S.diagram.rCellCount) := fun F =>
    if h : ∃ o, ∃ z : P.contactMap.Dart, P.contactMap.faceOf z = F ∧
        S.diagram.toCombMap.faceOf z.1 = OsinLemma94RealizedPolygons.objectFace S o
    then Classical.choose h else none
  have hg : ∀ F, ∃ z : P.contactMap.Dart, P.contactMap.faceOf z = F ∧
      S.diagram.toCombMap.faceOf z.1 = OsinLemma94RealizedPolygons.objectFace S (g F) := by
    intro F
    obtain ⟨z, hz, hcol⟩ := exists_object_dart P F
    obtain ⟨o, ho⟩ := P.exists_faceOf_eq_objectFace z hcol
    have h : ∃ o, ∃ z : P.contactMap.Dart, P.contactMap.faceOf z = F ∧
        S.diagram.toCombMap.faceOf z.1 = OsinLemma94RealizedPolygons.objectFace S o :=
      ⟨o, z, hz, ho⟩
    have hgF : g F = Classical.choose h := dif_pos h
    rw [hgF]
    exact Classical.choose_spec h
  refine (Finset.card_le_card_of_injOn g
    (fun F _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_).trans ?_
  · intro F hF F' hF' hgg
    obtain ⟨z, hz, ho⟩ := hg F
    obtain ⟨z', hz', ho'⟩ := hg F'
    rw [← hgg] at ho'
    exact outer_inj P (Finset.mem_filter.mp (Finset.mem_coe.mp hF)).2
      (Finset.mem_filter.mp (Finset.mem_coe.mp hF')).2 hz hz' ho ho'
  · simp [Finset.card_univ, Fintype.card_option]

end Charge

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces.holds_inj
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces.card_inner_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces.card_outer_le
