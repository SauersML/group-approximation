import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketTwoCollars
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionMultipleEdge
import GroupApproximation.Meta.AxiomGuard

/-!
# Geodesic collars on a pocket whose cycles need not follow their boundaries

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`, whose four sections must be `(λ, c)`-quasi-geodesic.

`GeodesicCollarStatement` (`SurgeryGeodesicCollar.lean`) inserts a collar along a side of a pocket
region whose face set and complement follow their boundary walks, and returns a following pocket.
At a full source arc in a lake, the complement cycle does not follow (`OsinPocketFullArcLakeModel`).
The multiple-edge cut builder without following cycles, through the component-route transports of
lane w1-binder-6, therefore needs a collar that neither asks for nor returns following cycles.

* `GeodesicCollarEulerOutput`: `GeodesicCollarOutput` without the two following conjuncts.
* `GeodesicCollarEulerStatement` (named residual, not proved here): the collar insertion along one
  side of a pocket region of a least-area diagram, with no following hypothesis.
* `PocketRegion.exists_twoCollars_of_ne_or_euler`: collars on both sides, over the Euler
  collar, as `exists_twoCollars_of_ne_or` over the following one.

Model test (paper).
* The collar cuts the map along the path `s` and glues in a strip of G-faces reading `s⁻¹ g`.
* Cutting along a path and gluing a disc along it keeps a planar map planar, whether or not the
  cycles of the pocket follow.
* At a vertex where the complement meets itself, as at the touch vertex of a lake, the strip is
  glued in the corner of `s` on the walk, which the walk order fixes.
* No counterexample is known.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The output of a collar insertion without following cycles**: `GeodesicCollarOutput` without
`P''.inner.FollowsBoundary` and `P''.outer.FollowsBoundary`. -/
def GeodesicCollarEulerOutput (D : RelGenSet G Lambda) {Delta : DiscDiagram.{u, w, v} W}
    (P : PocketRegion Delta) (rest : List Delta.toCombMap.Dart) (g : List (RelLetter G Lambda)) :
    Prop :=
  ∃ (Delta'' : DiscDiagram.{u, w, v} W) (E : OEquivalentDiscDiagram Delta Delta'')
    (P'' : PocketRegion Delta'') (collar : List Delta''.toCombMap.Dart)
    (ι : Delta.toCombMap.Dart ↪ Delta''.toCombMap.Dart),
    (∀ d, D.IsLetter (Delta''.label d)) ∧
    Embedded.invDarts Delta'' P''.outer.cycle = collar ++ rest.map ι ∧
    Embedded.dartWord Delta'' collar = g ∧
    (∀ d, Delta''.toCombMap.alpha (ι d) = ι (Delta.toCombMap.alpha d)) ∧
    (∀ d, Delta''.label (ι d) = Delta.label d) ∧
    Embedded.outerDarts Delta'' = (Embedded.outerDarts Delta).map ι ∧
    (∀ i : Fin Delta.rCellCount, (Embedded.cell Delta i).face ∈ P.outside →
      Embedded.cellDarts Delta'' (E.cellIndex i) = (Embedded.cellDarts Delta i).map ι) ∧
    (∀ i : Fin Delta.rCellCount,
      (Embedded.cell Delta'' (E.cellIndex i)).face ∈ P''.faces ↔
        (Embedded.cell Delta i).face ∈ P.faces)

/-- **A geodesic collar along a side of a pocket, without following cycles** (named residual).  As
`GeodesicCollarStatement`, for a pocket region of a least-area diagram, with no hypothesis that the
face set or its complement follows its boundary walk, and with an output that need not follow. -/
def GeodesicCollarEulerStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda), (∀ x ∈ D.base, x⁻¹ ∈ D.base) →
    ∀ (Delta : DiscDiagram.{u, w, v} W), (∀ d, D.IsLetter (Delta.label d)) → Delta.LeastArea →
    ∀ (P : PocketRegion Delta) (s rest : List Delta.toCombMap.Dart),
      Embedded.invDarts Delta P.outer.cycle = s ++ rest →
    ∀ (g : List (RelLetter G Lambda)), (∀ letter ∈ g, D.IsLetter letter) →
      RelLetter.listVal g = RelLetter.listVal (Embedded.dartWord Delta s) →
      (s = [] → g = []) → (g ≠ [] ∨ rest ≠ []) →
      GeodesicCollarEulerOutput D P rest g

namespace PocketRegion

/-- **Geodesic collars on both sides of a pocket, without following cycles**: as
`exists_twoCollars_of_ne_or`, over `GeodesicCollarEulerStatement`, for a least-area diagram. -/
theorem exists_twoCollars_of_ne_or_euler (hcollar : GeodesicCollarEulerStatement.{u, w, v})
    (D : RelGenSet G Lambda) (hinv : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {Delta : DiscDiagram.{u, w, v} W} (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (hlea : Delta.LeastArea) (P : PocketRegion Delta)
    {s₁ t₁ s₂ t₂ : List Delta.toCombMap.Dart}
    (hdecomposition : Embedded.invDarts Delta P.outer.cycle = s₁ ++ t₁ ++ s₂ ++ t₂)
    (hne : t₁ ≠ [] ∨ t₂ ≠ [] ∨ RelLetter.listVal (Embedded.dartWord Delta s₁) ≠ 1 ∨
      RelLetter.listVal (Embedded.dartWord Delta s₂) ≠ 1)
    {g₁ g₂ : List (RelLetter G Lambda)} (hg₁ : ∀ l ∈ g₁, D.IsLetter l)
    (hg₂ : ∀ l ∈ g₂, D.IsLetter l)
    (hval₁ : RelLetter.listVal g₁ = RelLetter.listVal (Embedded.dartWord Delta s₁))
    (hval₂ : RelLetter.listVal g₂ = RelLetter.listVal (Embedded.dartWord Delta s₂))
    (hnil₁ : s₁ = [] → g₁ = []) (hnil₂ : s₂ = [] → g₂ = []) :
    ∃ (Delta'' : DiscDiagram.{u, w, v} W) (E : OEquivalentDiscDiagram Delta Delta'')
      (P'' : PocketRegion Delta'') (c₁ c₂ : List Delta''.toCombMap.Dart)
      (ι : Delta.toCombMap.Dart ↪ Delta''.toCombMap.Dart),
      (∀ d, D.IsLetter (Delta''.label d)) ∧
      Embedded.invDarts Delta'' P''.outer.cycle = c₁ ++ t₁.map ι ++ c₂ ++ t₂.map ι ∧
      Embedded.dartWord Delta'' c₁ = g₁ ∧ Embedded.dartWord Delta'' c₂ = g₂ ∧
      (∀ d, Delta''.toCombMap.alpha (ι d) = ι (Delta.toCombMap.alpha d)) ∧
      (∀ d, Delta''.label (ι d) = Delta.label d) ∧
      Embedded.outerDarts Delta'' = (Embedded.outerDarts Delta).map ι ∧
      (∀ i : Fin Delta.rCellCount, (Embedded.cell Delta i).face ∈ P.outside →
        Embedded.cellDarts Delta'' (E.cellIndex i) = (Embedded.cellDarts Delta i).map ι) ∧
      (∀ i : Fin Delta.rCellCount,
        (Embedded.cell Delta'' (E.cellIndex i)).face ∈ P''.faces ↔
          (Embedded.cell Delta i).face ∈ P.faces) := by
  -- The collar along `s₁`; a side of value `≠ 1` makes `g₁` or `s₂` nonempty.
  have hne₁ : g₁ ≠ [] ∨ t₁ ++ s₂ ++ t₂ ≠ [] := by
    rcases hne with h | h | h | h
    · exact Or.inr fun hs => h (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hs).1).1
    · exact Or.inr fun hs => h (List.append_eq_nil_iff.mp hs).2
    · exact Or.inl fun hg => h (by simpa [hg, RelLetter.listVal] using hval₁.symm)
    · refine Or.inr fun hs => h ?_
      have hs₂ : s₂ = [] := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hs).1).2
      simp [hs₂, Embedded.dartWord, RelLetter.listVal]
  obtain ⟨Delta₁, E₁, P₁, c₁, ι₁, hlabel₁, hdec₁, hword₁, halpha₁, hlab₁, houter₁, hcells₁,
      hfaces₁⟩ :=
    hcollar D hinv Delta hlabel hlea P s₁ (t₁ ++ s₂ ++ t₂)
      (by rw [hdecomposition]; simp only [List.append_assoc]) g₁ hg₁ hval₁ hnil₁ hne₁
  -- Restart the complement cycle at the image of `s₂`.
  have hrot₁ : Embedded.invDarts Delta₁ P₁.outer.cycle ~r
      (s₂.map ι₁ ++ (t₂.map ι₁ ++ c₁ ++ t₁.map ι₁)) := by
    rw [hdec₁]
    have h := List.isRotated_append (l := c₁ ++ t₁.map ι₁) (l' := s₂.map ι₁ ++ t₂.map ι₁)
    simpa only [List.map_append, List.append_assoc] using h
  have hval₂' : RelLetter.listVal g₂ =
      RelLetter.listVal (Embedded.dartWord Delta₁ (s₂.map ι₁)) := by
    rw [Embedded.dartWord_map_embedding ι₁ hlab₁]
    exact hval₂
  -- The collar along the image of `s₂`; a side of value `≠ 1` makes `g₂` or `c₁` nonempty.
  have hne₂ : g₂ ≠ [] ∨ t₂.map ι₁ ++ c₁ ++ t₁.map ι₁ ≠ [] := by
    rcases hne with h | h | h | h
    · exact Or.inr fun hs => h (List.map_eq_nil_iff.mp (List.append_eq_nil_iff.mp hs).2)
    · exact Or.inr fun hs => h (List.map_eq_nil_iff.mp
        (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hs).1).1)
    · refine Or.inr fun hs => h ?_
      have hc₁ : c₁ = [] := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hs).1).2
      have hg : g₁ = [] := by simpa [hc₁, Embedded.dartWord] using hword₁.symm
      simpa [hg, RelLetter.listVal] using hval₁.symm
    · exact Or.inl fun hg => h (by simpa [hg, RelLetter.listVal] using hval₂.symm)
  obtain ⟨Delta₂, E₂, P₂, c₂, ι₂, hlabel₂, hdec₂, hword₂, halpha₂, hlab₂, houter₂, hcells₂,
      hfaces₂⟩ :=
    hcollar D hinv Delta₁ hlabel₁ (E₁.leastArea hlea) (P₁.withOuter hrot₁) (s₂.map ι₁)
      (t₂.map ι₁ ++ c₁ ++ t₁.map ι₁) (P₁.invDarts_withOuter_cycle hrot₁) g₂ hg₂ hval₂'
      (fun h => hnil₂ (List.map_eq_nil_iff.mp h)) hne₂
  -- Restart the complement cycle at the first collar.
  have hrot₂ : Embedded.invDarts Delta₂ P₂.outer.cycle ~r
      (c₁.map ι₂ ++ t₁.map (ι₁.trans ι₂) ++ c₂ ++ t₂.map (ι₁.trans ι₂)) := by
    rw [hdec₂]
    have h := List.isRotated_append (l := c₂ ++ t₂.map (ι₁.trans ι₂))
      (l' := c₁.map ι₂ ++ t₁.map (ι₁.trans ι₂))
    simpa only [List.map_append, List.map_map, Function.Embedding.coe_trans,
      List.append_assoc] using h
  refine ⟨Delta₂, E₁.trans E₂, P₂.withOuter hrot₂, c₁.map ι₂, c₂, ι₁.trans ι₂, hlabel₂,
    P₂.invDarts_withOuter_cycle hrot₂, ?_, hword₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Embedded.dartWord_map_embedding ι₂ hlab₂]
    exact hword₁
  · intro d
    show Delta₂.toCombMap.alpha (ι₂ (ι₁ d)) = ι₂ (ι₁ (Delta.toCombMap.alpha d))
    rw [halpha₂, halpha₁]
  · intro d
    show Delta₂.label (ι₂ (ι₁ d)) = Delta.label d
    rw [hlab₂, hlab₁]
  · rw [houter₂, houter₁, List.map_map, Function.Embedding.coe_trans]
  · intro i hi
    have hi₁ : (Embedded.cell Delta₁ (E₁.cellIndex i)).face ∈ (P₁.withOuter hrot₁).outside := by
      rw [P₁.withOuter_outside hrot₁, P₁.mem_outside_iff]
      exact fun hf => (P.mem_outside_iff _).mp hi ((hfaces₁ i).mp hf)
    show Embedded.cellDarts Delta₂ (E₂.cellIndex (E₁.cellIndex i)) = _
    rw [hcells₂ (E₁.cellIndex i) hi₁, hcells₁ i hi, List.map_map, Function.Embedding.coe_trans]
  · intro i
    exact (hfaces₂ (E₁.cellIndex i)).trans (hfaces₁ i)

end PocketRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollarEulerOutput
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollarEulerStatement
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.exists_twoCollars_of_ne_or_euler
