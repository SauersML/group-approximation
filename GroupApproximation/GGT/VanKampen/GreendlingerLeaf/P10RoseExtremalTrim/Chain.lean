import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkChain
import GroupApproximation.Meta.AxiomGuard

/-!
# The listing `s₁ t₁⁻¹ s₂ t₂` is a walk once its sides and three junctions are

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-09, part (a).

Let `t₁` be an arc of a relator cell and `t₂` an arc of the oriented outer boundary.  The darts of
an arc of a closed walk form a walk (`Embedded.CyclicArc.isChain_darts`), a walk read backwards is
a walk (`Embedded.isChain_invDarts`), and cell boundaries and the outer boundary are closed walks
(`Embedded.isChain_closes_cellDarts`, `Embedded.isChain_closes_outerDarts`), so `t₁⁻¹` and `t₂`
are always walks.  Hence `s₁ ++ t₁⁻¹ ++ s₂ ++ t₂` is a walk as soon as `s₁`, `s₂` are walks and
the three junctions `s₁ | t₁⁻¹`, `s₁ t₁⁻¹ | s₂`, `s₁ t₁⁻¹ s₂ | t₂` meet at a vertex
(`List.isChain_append`, applied three times).  The fourth junction `t₂ | s₁` (the closing
equation) is supplied by balance in `P10RoseExtremal/Close`.

* `isChain_listing_of_junctions`: the assembly above.
* `junctions_of_isChain_listing`: conversely, a walk listing has walk sides and meeting junctions
  (used only to certify that the trimmed residual of `P10RoseExtremalTrim/Reduction` is implied by
  `P10RoseExtremal.RoseExtremalRegionStatement`).

The junctions are stated with `getLast?`/`head?`, so they are vacuous across an empty block
(`s₁ = []`, `t₁` of length `0`, ...); the prefixes in the second and third junctions make the
statement correct for every pattern of empty blocks.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The block listing is a walk from its sides and three junctions.**  The blocks `t₁⁻¹` and
`t₂` are walks automatically; the sides `s₁`, `s₂` and the three junctions are the input. -/
theorem isChain_listing_of_junctions {X : DiscDiagram.{u, w, v} W} {source : Fin X.rCellCount}
    (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
    {s₁ s₂ : List X.toCombMap.Dart}
    (hs₁ : s₁.IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e)
    (hs₂ : s₂.IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e)
    (hj₁ : ∀ a ∈ s₁.getLast?, ∀ b ∈ (invDarts X t₁.darts).head?,
      X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b)
    (hj₂ : ∀ a ∈ (s₁ ++ invDarts X t₁.darts).getLast?, ∀ b ∈ s₂.head?,
      X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b)
    (hj₃ : ∀ a ∈ (s₁ ++ invDarts X t₁.darts ++ s₂).getLast?, ∀ b ∈ t₂.darts.head?,
      X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) :
    (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := by
  obtain ⟨hcell, hcellc⟩ := isChain_closes_cellDarts X source
  obtain ⟨hout, houtc⟩ := isChain_closes_outerDarts X
  have hinv := isChain_invDarts (Delta := X) (t₁.isChain_darts hcell hcellc)
  have ht₂ := t₂.isChain_darts hout houtc
  exact List.isChain_append.mpr ⟨List.isChain_append.mpr ⟨List.isChain_append.mpr
    ⟨hs₁, hinv, hj₁⟩, hs₂, hj₂⟩, ht₂, hj₃⟩

/-- **A walk listing has walk sides and meeting junctions.** -/
theorem junctions_of_isChain_listing {X : DiscDiagram.{u, w, v} W} {source : Fin X.rCellCount}
    (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
    {s₁ s₂ : List X.toCombMap.Dart}
    (h : (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) :
    (s₁.IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
    (s₂.IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
    (∀ a ∈ s₁.getLast?, ∀ b ∈ (invDarts X t₁.darts).head?,
      X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
    (∀ a ∈ (s₁ ++ invDarts X t₁.darts).getLast?, ∀ b ∈ s₂.head?,
      X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
    (∀ a ∈ (s₁ ++ invDarts X t₁.darts ++ s₂).getLast?, ∀ b ∈ t₂.darts.head?,
      X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) := by
  obtain ⟨h₁₂₃, -, hj₃⟩ := List.isChain_append.mp h
  obtain ⟨h₁₂, hs₂, hj₂⟩ := List.isChain_append.mp h₁₂₃
  obtain ⟨hs₁, -, hj₁⟩ := List.isChain_append.mp h₁₂
  exact ⟨hs₁, hs₂, hj₁, hj₂, hj₃⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.isChain_listing_of_junctions
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.junctions_of_isChain_listing
