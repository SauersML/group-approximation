import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollar
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFollowsBoundary
import GroupApproximation.GGT.VanKampen.Estimating.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Geodesic collars on both sides of a pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`, whose four sections must be `(λ, c)`-quasi-geodesic.  Both sides are
replaced by G-face collars reading words `g_1`, `g_2` of the same values, so that the boundary
of the new pocket reads `g_1 t_1 g_2 t_2`.

* `Embedded.dartWord_map_embedding`: an embedding of darts preserving the labels preserves the
  words.
* `PocketRegion.exists_twoCollars`: the collar insertion `GeodesicCollarStatement` (lane
  `kh-torsion`, a hypothesis here) along `s_1`, then, after restarting the complement cycle with
  `PocketRegion.withOuter`, along the image of `s_2`, and a final restart.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace Embedded

/-- An embedding of darts preserving the labels preserves the words read on lists of darts. -/
theorem dartWord_map_embedding {Delta Delta' : DiscDiagram.{u, w, v} W}
    (ι : Delta.toCombMap.Dart ↪ Delta'.toCombMap.Dart)
    (hlabel : ∀ d, Delta'.label (ι d) = Delta.label d) (l : List Delta.toCombMap.Dart) :
    dartWord Delta' (l.map ι) = dartWord Delta l := by
  simp only [dartWord, List.map_map, Function.comp_def, hlabel]

end Embedded

namespace PocketRegion

/-- **Geodesic collars on both sides of a pocket** (W1, Osin Lemma 9.7(b), for lane
`hull-select`'s MultipleEdgeCut assembly).  Let `P` be a pocket region of `Δ` whose face set and
complement follow their boundary walks, with inverse complement cycle `s₁ t₁ s₂ t₂` and `t₁`,
`t₂` nonempty.  Let `g₁`, `g₂` be words in the letters of `D` with the values of `s₁`, `s₂`,
empty when the side is.  Given the collar insertion, there is an O-equivalent diagram `Δ''` with
a pocket region `P''` whose inverse complement cycle reads `c₁ t₁ c₂ t₂`: `c₁` and `c₂` read `g₁`
and `g₂`, and `t₁`, `t₂` are carried by an embedding of darts compatible with `alpha` and the
labels.  The outer boundary and the relator cells outside `P` keep their darts, and every relator
cell stays on its side of the pocket. -/
theorem exists_twoCollars (hcollar : GeodesicCollarStatement.{u, w, v})
    (D : RelGenSet G Lambda) (hinv : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {Delta : DiscDiagram.{u, w, v} W} (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (P : PocketRegion Delta) (hin : P.inner.FollowsBoundary) (hout : P.outer.FollowsBoundary)
    {s₁ t₁ s₂ t₂ : List Delta.toCombMap.Dart}
    (hdecomposition : Embedded.invDarts Delta P.outer.cycle = s₁ ++ t₁ ++ s₂ ++ t₂)
    (ht₁ : t₁ ≠ []) (ht₂ : t₂ ≠ [])
    {g₁ g₂ : List (RelLetter G Lambda)} (hg₁ : ∀ l ∈ g₁, D.IsLetter l)
    (hg₂ : ∀ l ∈ g₂, D.IsLetter l)
    (hval₁ : RelLetter.listVal g₁ = RelLetter.listVal (Embedded.dartWord Delta s₁))
    (hval₂ : RelLetter.listVal g₂ = RelLetter.listVal (Embedded.dartWord Delta s₂))
    (hnil₁ : s₁ = [] → g₁ = []) (hnil₂ : s₂ = [] → g₂ = []) :
    ∃ (Delta'' : DiscDiagram.{u, w, v} W) (E : OEquivalentDiscDiagram Delta Delta'')
      (P'' : PocketRegion Delta'') (c₁ c₂ : List Delta''.toCombMap.Dart)
      (ι : Delta.toCombMap.Dart ↪ Delta''.toCombMap.Dart),
      (∀ d, D.IsLetter (Delta''.label d)) ∧ P''.inner.FollowsBoundary ∧
      P''.outer.FollowsBoundary ∧
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
  -- The collar along `s₁`.
  obtain ⟨Delta₁, E₁, P₁, c₁, ι₁, hlabel₁, hin₁, hout₁, hdec₁, hword₁, halpha₁, hlab₁,
      houter₁, hcells₁, hfaces₁⟩ :=
    hcollar D hinv Delta hlabel P hin hout s₁ (t₁ ++ s₂ ++ t₂)
      (by rw [hdecomposition]; simp only [List.append_assoc]) g₁ hg₁ hval₁ hnil₁
      (Or.inr fun h => ht₁ (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).1)
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
  -- The collar along the image of `s₂`.
  obtain ⟨Delta₂, E₂, P₂, c₂, ι₂, hlabel₂, hin₂, hout₂, hdec₂, hword₂, halpha₂, hlab₂,
      houter₂, hcells₂, hfaces₂⟩ :=
    hcollar D hinv Delta₁ hlabel₁ (P₁.withOuter hrot₁) hin₁
      ((P₁.withOuter_outer_followsBoundary_iff hrot₁).mpr hout₁) (s₂.map ι₁)
      (t₂.map ι₁ ++ c₁ ++ t₁.map ι₁) (P₁.invDarts_withOuter_cycle hrot₁) g₂ hg₂ hval₂'
      (fun h => hnil₂ (List.map_eq_nil_iff.mp h))
      (Or.inr fun h => ht₂ (List.map_eq_nil_iff.mp
        (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).1))
  -- Restart the complement cycle at the first collar.
  have hrot₂ : Embedded.invDarts Delta₂ P₂.outer.cycle ~r
      (c₁.map ι₂ ++ t₁.map (ι₁.trans ι₂) ++ c₂ ++ t₂.map (ι₁.trans ι₂)) := by
    rw [hdec₂]
    have h := List.isRotated_append (l := c₂ ++ t₂.map (ι₁.trans ι₂))
      (l' := c₁.map ι₂ ++ t₁.map (ι₁.trans ι₂))
    simpa only [List.map_append, List.map_map, Function.Embedding.coe_trans,
      List.append_assoc] using h
  refine ⟨Delta₂, E₁.trans E₂, P₂.withOuter hrot₂, c₁.map ι₂, c₂, ι₁.trans ι₂, hlabel₂, hin₂,
    (P₂.withOuter_outer_followsBoundary_iff hrot₂).mpr hout₂, P₂.invDarts_withOuter_cycle hrot₂,
    ?_, hword₂, ?_, ?_, ?_, ?_, ?_⟩
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

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.dartWord_map_embedding
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.exists_twoCollars
