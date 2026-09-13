import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarDouble
import GroupApproximation.Meta.AxiomGuard

/-!
# The strip on a long side

Stage 1 of the collar insertion (`GeodesicCollar.StripStatement`) for a side `s` of any length.
`stripSingleton` gives the strip on the first dart of `s`, and the pinch step
(`GeodesicCollar.StripStepStatement`) moves one dart from the rest of the walk to the side of the
strip.  `stripAppend` repeats the step along a list `t`, composing the transports
(`Transport.trans`), and `stripStatement_of_step` assembles Stage 1.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

universe u w v

namespace GroupApproximation.GGT.VanKampen.GeodesicCollar

open Surgery.MapCollapse

/-- **The pinch step.**  A strip along `p` whose remaining walk starts with `d` has a transport to a
strip along the image of `p ++ [d]`. -/
def StripStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda), (∀ x ∈ D.base, x⁻¹ ∈ D.base) →
    ∀ (Delta : DiscDiagram.{u, w, v} W), (∀ d, D.IsLetter (Delta.label d)) →
    ∀ (S : Finset Delta.toCombMap.Face) (p : List Delta.toCombMap.Dart)
      (d : Delta.toCombMap.Dart) (r : List Delta.toCombMap.Dart), Strip Delta S p (d :: r) →
      ∃ (Delta' : DiscDiagram.{u, w, v} W) (S' : Finset Delta'.toCombMap.Face)
        (T : Transport D S Delta' S'),
        Nonempty (Strip Delta' S' ((p ++ [d]).map T.embedding) (r.map T.embedding))

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The pinch step along a list.**  A strip along `p` whose remaining walk is `t ++ rest` has a
transport to a strip along the image of `p ++ t`. -/
theorem stripAppend (hstep : StripStepStatement.{u, w, v}) (D : RelGenSet G Lambda)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (n : ℕ) :
    ∀ (Delta : DiscDiagram.{u, w, v} W), (∀ d, D.IsLetter (Delta.label d)) →
    ∀ (S : Finset Delta.toCombMap.Face) (p t rest : List Delta.toCombMap.Dart), t.length = n →
      Strip Delta S p (t ++ rest) →
      ∃ (Delta' : DiscDiagram.{u, w, v} W) (S' : Finset Delta'.toCombMap.Face)
        (T : Transport D S Delta' S'),
        Nonempty (Strip Delta' S' ((p ++ t).map T.embedding) (rest.map T.embedding)) := by
  induction n with
  | zero =>
    intro Delta hlabel S p t rest ht X
    obtain rfl := List.eq_nil_of_length_eq_zero ht
    refine ⟨Delta, S, Transport.refl D hlabel S, ⟨?_⟩⟩
    have hp : (p ++ []).map (Transport.refl D hlabel S).embedding = p := by
      rw [List.append_nil]
      exact List.map_id p
    have hr : rest.map (Transport.refl D hlabel S).embedding = rest := List.map_id rest
    rw [hp, hr]
    exact X
  | succ n ih =>
    intro Delta hlabel S p t rest ht X
    rcases t with _ | ⟨d, t⟩
    · simp at ht
    · obtain ⟨Delta₁, S₁, T₁, ⟨X₁⟩⟩ := hstep D hsymm Delta hlabel S p d (t ++ rest) X
      rw [List.map_append (l₁ := t) (l₂ := rest)] at X₁
      have ht' : (t.map T₁.embedding).length = n := by
        rw [List.length_map]
        simpa using ht
      obtain ⟨Delta₂, S₂, T₂, ⟨X₂⟩⟩ := ih Delta₁ T₁.label_isLetter S₁
        ((p ++ [d]).map T₁.embedding) (t.map T₁.embedding) (rest.map T₁.embedding) ht' X₁
      refine ⟨Delta₂, S₂, T₁.trans T₂, ⟨?_⟩⟩
      have hp : ((p ++ [d]).map T₁.embedding ++ t.map T₁.embedding).map T₂.embedding =
          (p ++ d :: t).map (T₁.trans T₂).embedding := by
        rw [← List.map_append, List.map_map, List.append_assoc, List.singleton_append]
        rfl
      have hr : (rest.map T₁.embedding).map T₂.embedding = rest.map (T₁.trans T₂).embedding := by
        rw [List.map_map]
        rfl
      rw [← hp, ← hr]
      exact X₂

/-- **Stage 1 from the pinch step.**  The strip on the first dart of the side (`stripSingleton`),
followed by the pinch step along the remaining darts of the side (`stripAppend`). -/
theorem stripStatement_of_step (hstep : StripStepStatement.{u, w, v}) :
    StripStatement.{u, w, v} := by
  intro G _ Lambda W D hsymm Delta hlabel S s rest hs hwalk hB hout
  obtain ⟨d, t, rfl⟩ := List.exists_cons_of_ne_nil hs
  obtain ⟨Delta₁, S₁, T₁, ⟨X₁⟩⟩ :=
    stripSingleton D hsymm Delta hlabel S d (t ++ rest) hwalk hB hout
  rw [List.map_append (l₁ := t) (l₂ := rest)] at X₁
  obtain ⟨Delta₂, S₂, T₂, ⟨X₂⟩⟩ := stripAppend hstep D hsymm (t.map T₁.embedding).length Delta₁
    T₁.label_isLetter S₁ ([d].map T₁.embedding) (t.map T₁.embedding) (rest.map T₁.embedding) rfl X₁
  refine ⟨Delta₂, S₂, T₁.trans T₂, ⟨?_⟩⟩
  have hs' : ([d].map T₁.embedding ++ t.map T₁.embedding).map T₂.embedding =
      (d :: t).map (T₁.trans T₂).embedding := by
    rw [← List.map_append, List.map_map, List.singleton_append]
    rfl
  have hr : (rest.map T₁.embedding).map T₂.embedding = rest.map (T₁.trans T₂).embedding := by
    rw [List.map_map]
    rfl
  rw [← hs', ← hr]
  exact X₂

end GroupApproximation.GGT.VanKampen.GeodesicCollar

#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.stripAppend
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.stripStatement_of_step
