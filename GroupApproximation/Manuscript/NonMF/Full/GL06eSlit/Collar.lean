import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketTwoCollars
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCollarOfGeodesic
import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarStripStep
import GroupApproximation.GGT.OsinGeodesicWord
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06e, step 2b: geodesic collars on the three sides of a slit seed

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the all-cells case.  Infrastructure for
`thm:hull` (non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7).  Part (2b) of the split in `research/artifacts/gq-ms-nm-gl06e-step2-split.md`.

A *seed* is a pocket region `P` whose two cycles follow their boundary walks, with inverse
complement cycle `g ++ s₁ ++ t ++ s₂`, where `t = invDarts arc` for a nonempty arc of a relator
cell `Π` outside `P`.  The collar insertion is proved (`geodesicCollarStatement_holds`), so every
side other than `t` can be re-spelled by any word of the same value.

* `ArcCarry.transport`, `ArcCarry.transport_darts`: an arc of a cycle, carried to the image
  cycle under a dart map.
* `exists_threeCollars`: given words `w₀`, `w₁`, `w₂` with the values of `g`, `s₁`, `s₂` (empty
  when the side is), there is an O-equivalent copy with a pocket whose two cycles follow, with
  inverse complement cycle `c₀ ++ c₁ ++ invDarts arc' ++ c₂`, where `cᵢ` reads `wᵢ` and `arc'` is
  the carried arc of the image of `Π`.  It uses `PocketRegion.exists_twoCollars_of_ne_or` twice:
  once on `s₁`, `s₂` around `t`, then on `g`.
* `exists_geodesicCollars`: the same, with geodesic words for the three values.  Each new side is
  then a geodesic spelling of its own value, of length the word norm of the old side's value.

What (2b) does not yet give: the feet of the slits on the boundary (the collar output carries no
vertex correspondence), and the slit-minimality fields, whose form awaits the κ-slack decision
(board `nm-gl06e.md`).

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06eSlit

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded

/-! ## Carrying a cyclic arc to an image cycle -/

namespace ArcCarry

/-- The same arc, on the image of the cycle under a dart map. -/
def transport {α β : Type v} {cycle : List α} {cycle' : List β} (f : α → β)
    (h : cycle' = cycle.map f) (arc : CyclicArc cycle) : CyclicArc cycle' where
  start := Fin.cast (by rw [h, List.length_map]) arc.start
  length := arc.length
  length_le := by rw [h, List.length_map]; exact arc.length_le

theorem transport_length {α β : Type v} {cycle : List α} {cycle' : List β} (f : α → β)
    (h : cycle' = cycle.map f) (arc : CyclicArc cycle) :
    (transport f h arc).length = arc.length :=
  rfl

/-- The carried arc has the image darts. -/
theorem transport_darts {α β : Type v} {cycle : List α} {cycle' : List β} (f : α → β)
    (h : cycle' = cycle.map f) (arc : CyclicArc cycle) :
    (transport f h arc).darts = arc.darts.map f := by
  subst h
  simp [CyclicArc.darts, CyclicArc.rotated, transport]

end ArcCarry

section Collars

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- A geodesic word for the value of an empty side is empty. -/
theorem eq_nil_of_isGeodesicWord_nil {D : RelGenSet G Lambda} {X : DiscDiagram.{u, w, v} W}
    {s : List X.toCombMap.Dart} {w' : List (RelLetter G Lambda)}
    (hw : OsinComponents.IsGeodesicWord D 1 (RelLetter.listVal (dartWord X s)) w')
    (hs : s = []) : w' = [] := by
  subst hs
  have h1 : RelLetter.listVal (dartWord X ([] : List X.toCombMap.Dart)) = 1 := by
    simp [Embedded.dartWord, RelLetter.listVal]
  rw [h1] at hw
  have hlen := hw.2.2
  rw [WordMetric.wordDist_self] at hlen
  exact List.eq_nil_of_length_eq_zero hlen

/-- The value of a geodesic word is the value it spells. -/
theorem listVal_of_isGeodesicWord {D : RelGenSet G Lambda} {x : G}
    {w' : List (RelLetter G Lambda)} (hw : OsinComponents.IsGeodesicWord D 1 x w') :
    RelLetter.listVal w' = x := by
  have h := hw.2.1
  rwa [one_mul] at h

/-- **Collars on the three sides of a slit seed** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121).  The sides `g`, `s₁`, `s₂` of a seed pocket are re-spelled by
words `w₀`, `w₁`, `w₂` of the same values; the arc `t` of the cell `Π` outside the pocket is
carried along, and every relator cell stays on its side. -/
theorem exists_threeCollars (D : RelGenSet G Lambda) (hinv : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {Delta : DiscDiagram.{u, w, v} W} (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (P : PocketRegion Delta) (hin : P.inner.FollowsBoundary) (hout : P.outer.FollowsBoundary)
    {nearest : Fin Delta.rCellCount} (hnear : (cell Delta nearest).face ∉ P.faces)
    (arc : CyclicArc (cellDarts Delta nearest)) (harc : arc.darts ≠ [])
    {g s₁ s₂ : List Delta.toCombMap.Dart}
    (hdec : invDarts Delta P.outer.cycle = g ++ s₁ ++ invDarts Delta arc.darts ++ s₂)
    {w₀ w₁ w₂ : List (RelLetter G Lambda)}
    (hl₀ : ∀ l ∈ w₀, D.IsLetter l) (hl₁ : ∀ l ∈ w₁, D.IsLetter l) (hl₂ : ∀ l ∈ w₂, D.IsLetter l)
    (hv₀ : RelLetter.listVal w₀ = RelLetter.listVal (dartWord Delta g))
    (hv₁ : RelLetter.listVal w₁ = RelLetter.listVal (dartWord Delta s₁))
    (hv₂ : RelLetter.listVal w₂ = RelLetter.listVal (dartWord Delta s₂))
    (hn₀ : g = [] → w₀ = []) (hn₁ : s₁ = [] → w₁ = []) (hn₂ : s₂ = [] → w₂ = []) :
    ∃ (X : DiscDiagram.{u, w, v} W) (E : OEquivalentDiscDiagram Delta X) (Q : PocketRegion X)
      (c₀ c₁ c₂ : List X.toCombMap.Dart) (arc' : CyclicArc (cellDarts X (E.cellIndex nearest))),
      (∀ d, D.IsLetter (X.label d)) ∧ Q.inner.FollowsBoundary ∧ Q.outer.FollowsBoundary ∧
      invDarts X Q.outer.cycle = c₀ ++ c₁ ++ invDarts X arc'.darts ++ c₂ ∧
      dartWord X c₀ = w₀ ∧ dartWord X c₁ = w₁ ∧ dartWord X c₂ = w₂ ∧
      arc'.length = arc.length ∧
      (∀ i : Fin Delta.rCellCount,
        (cell X (E.cellIndex i)).face ∈ Q.faces ↔ (cell Delta i).face ∈ P.faces) := by
  have hT : invDarts Delta arc.darts ≠ [] := by
    simpa [Embedded.invDarts] using harc
  -- First the two slits, around the arc, with the collar part `g` left in place.
  have hrot : invDarts Delta P.outer.cycle ~r
      (s₁ ++ invDarts Delta arc.darts ++ s₂ ++ g) := by
    rw [hdec]
    have h := List.isRotated_append (l := g) (l' := s₁ ++ invDarts Delta arc.darts ++ s₂)
    simpa only [List.append_assoc] using h
  obtain ⟨X₁, E₁, P₁, c₁, c₂, ι₁, hlabel₁, hin₁, hout₁, hdec₁, hword₁, hword₂, halpha₁, hlab₁,
      _houter₁, hcells₁, hfaces₁⟩ :=
    PocketRegion.exists_twoCollars_of_ne_or
      GeodesicCollar.StripStep.geodesicCollarStatement_holds D hinv hlabel (P.withOuter hrot) hin
      ((P.withOuter_outer_followsBoundary_iff hrot).mpr hout) (P.invDarts_withOuter_cycle hrot)
      (Or.inl hT) hl₁ hl₂ hv₁ hv₂ hn₁ hn₂
  -- Then the collar part, with everything else as its arc.
  have hT₁ : c₁ ++ (invDarts Delta arc.darts).map ι₁ ++ c₂ ≠ [] := by
    intro h
    exact hT (List.map_eq_nil_iff.mp (List.append_eq_nil_iff.mp
      (List.append_eq_nil_iff.mp h).1).2)
  have hrot₁ : invDarts X₁ P₁.outer.cycle ~r
      (g.map ι₁ ++ (c₁ ++ (invDarts Delta arc.darts).map ι₁ ++ c₂) ++ [] ++ []) := by
    rw [hdec₁]
    have h := List.isRotated_append (l := c₁ ++ (invDarts Delta arc.darts).map ι₁ ++ c₂)
      (l' := g.map ι₁)
    simpa only [List.append_assoc, List.append_nil] using h
  have hv₀' : RelLetter.listVal w₀ = RelLetter.listVal (dartWord X₁ (g.map ι₁)) := by
    rw [Embedded.dartWord_map_embedding ι₁ hlab₁]
    exact hv₀
  obtain ⟨X₂, E₂, P₂, c₀, c₃, ι₂, hlabel₂, hin₂, hout₂, hdec₂, hword₀, hword₃, halpha₂, hlab₂,
      _houter₂, hcells₂, hfaces₂⟩ :=
    PocketRegion.exists_twoCollars_of_ne_or
      GeodesicCollar.StripStep.geodesicCollarStatement_holds D hinv hlabel₁ (P₁.withOuter hrot₁)
      hin₁ ((P₁.withOuter_outer_followsBoundary_iff hrot₁).mpr hout₁)
      (P₁.invDarts_withOuter_cycle hrot₁) (Or.inl hT₁) (g₂ := []) hl₀ (fun _ h => by simp at h)
      hv₀' (by simp [Embedded.dartWord]) (fun h => hn₀ (List.map_eq_nil_iff.mp h)) (fun _ => rfl)
  have hc₃ : c₃ = [] := by
    have h : c₃.map X₂.label = [] := hword₃
    exact List.map_eq_nil_iff.mp h
  -- The arc of `Π` is carried to the image of `Π`.
  have hout₀ : (cell Delta nearest).face ∈ (P.withOuter hrot).outside := by
    rw [P.withOuter_outside hrot]
    exact (P.mem_outside_iff _).mpr hnear
  have hout₁' : (cell X₁ (E₁.cellIndex nearest)).face ∈ (P₁.withOuter hrot₁).outside := by
    rw [P₁.withOuter_outside hrot₁, P₁.mem_outside_iff]
    exact fun hf => hnear ((hfaces₁ nearest).mp hf)
  have hcells : cellDarts X₂ ((E₁.trans E₂).cellIndex nearest) =
      (cellDarts Delta nearest).map (fun d => ι₂ (ι₁ d)) := by
    show cellDarts X₂ (E₂.cellIndex (E₁.cellIndex nearest)) = _
    rw [hcells₂ (E₁.cellIndex nearest) hout₁', hcells₁ nearest hout₀, List.map_map]
    rfl
  have halpha : ∀ d, X₂.toCombMap.alpha (ι₂ (ι₁ d)) = ι₂ (ι₁ (Delta.toCombMap.alpha d)) := by
    intro d
    rw [halpha₂, halpha₁]
  refine ⟨X₂, E₁.trans E₂, P₂, c₀, c₁.map ι₂, c₂.map ι₂,
    ArcCarry.transport (fun d => ι₂ (ι₁ d)) hcells arc, hlabel₂, hin₂, hout₂, ?_, hword₀, ?_, ?_,
    rfl, ?_⟩
  · rw [hdec₂, hc₃, ArcCarry.transport_darts,
      Embedded.invDarts_map_of_alpha_comm (fun d => ι₂ (ι₁ d)) halpha]
    simp only [List.map_append, List.map_map, List.map_nil, List.append_nil, List.append_assoc,
      Function.comp_def]
  · rw [Embedded.dartWord_map_embedding ι₂ hlab₂]
    exact hword₁
  · rw [Embedded.dartWord_map_embedding ι₂ hlab₂]
    exact hword₂
  · intro i
    exact (hfaces₂ (E₁.cellIndex i)).trans (hfaces₁ i)

/-- **Geodesic collars on the three sides of a slit seed** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121).  `exists_threeCollars` with geodesic words for the
three values: each new side is a geodesic spelling of its own value, which is the value of the
old side. -/
theorem exists_geodesicCollars (D : RelGenSet G Lambda) (hinv : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {Delta : DiscDiagram.{u, w, v} W} (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (P : PocketRegion Delta) (hin : P.inner.FollowsBoundary) (hout : P.outer.FollowsBoundary)
    {nearest : Fin Delta.rCellCount} (hnear : (cell Delta nearest).face ∉ P.faces)
    (arc : CyclicArc (cellDarts Delta nearest)) (harc : arc.darts ≠ [])
    {g s₁ s₂ : List Delta.toCombMap.Dart}
    (hdec : invDarts Delta P.outer.cycle = g ++ s₁ ++ invDarts Delta arc.darts ++ s₂) :
    ∃ (X : DiscDiagram.{u, w, v} W) (E : OEquivalentDiscDiagram Delta X) (Q : PocketRegion X)
      (c₀ c₁ c₂ : List X.toCombMap.Dart) (arc' : CyclicArc (cellDarts X (E.cellIndex nearest))),
      (∀ d, D.IsLetter (X.label d)) ∧ Q.inner.FollowsBoundary ∧ Q.outer.FollowsBoundary ∧
      invDarts X Q.outer.cycle = c₀ ++ c₁ ++ invDarts X arc'.darts ++ c₂ ∧
      OsinComponents.IsGeodesicWord D 1 (RelLetter.listVal (dartWord Delta g)) (dartWord X c₀) ∧
      OsinComponents.IsGeodesicWord D 1 (RelLetter.listVal (dartWord Delta s₁)) (dartWord X c₁) ∧
      OsinComponents.IsGeodesicWord D 1 (RelLetter.listVal (dartWord Delta s₂)) (dartWord X c₂) ∧
      arc'.length = arc.length ∧
      (∀ i : Fin Delta.rCellCount,
        (cell X (E.cellIndex i)).face ∈ Q.faces ↔ (cell Delta i).face ∈ P.faces) := by
  obtain ⟨w₀, hw₀⟩ := OsinComponents.existsGeodesicWord D 1 (RelLetter.listVal (dartWord Delta g))
  obtain ⟨w₁, hw₁⟩ :=
    OsinComponents.existsGeodesicWord D 1 (RelLetter.listVal (dartWord Delta s₁))
  obtain ⟨w₂, hw₂⟩ :=
    OsinComponents.existsGeodesicWord D 1 (RelLetter.listVal (dartWord Delta s₂))
  obtain ⟨X, E, Q, c₀, c₁, c₂, arc', hlabel', hin', hout', hdec', h₀, h₁, h₂, hlen, hfaces⟩ :=
    exists_threeCollars D hinv hlabel P hin hout hnear arc harc hdec hw₀.1 hw₁.1 hw₂.1
      (listVal_of_isGeodesicWord hw₀) (listVal_of_isGeodesicWord hw₁)
      (listVal_of_isGeodesicWord hw₂) (eq_nil_of_isGeodesicWord_nil hw₀)
      (eq_nil_of_isGeodesicWord_nil hw₁) (eq_nil_of_isGeodesicWord_nil hw₂)
  refine ⟨X, E, Q, c₀, c₁, c₂, arc', hlabel', hin', hout', hdec', ?_, ?_, ?_, hlen, hfaces⟩
  · rw [h₀]; exact hw₀
  · rw [h₁]; exact hw₁
  · rw [h₂]; exact hw₂

end Collars

end GroupApproximation.Full.GL06eSlit

#audit_axioms GroupApproximation.Full.GL06eSlit.ArcCarry.transport_darts
#audit_axioms GroupApproximation.Full.GL06eSlit.exists_threeCollars
#audit_axioms GroupApproximation.Full.GL06eSlit.exists_geodesicCollars
