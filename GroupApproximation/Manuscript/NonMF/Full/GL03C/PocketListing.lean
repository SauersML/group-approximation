import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.Manuscript.NonMF.Full.GL03C.Listing

/-!
# The kept darts of a pocket boundary as `s₁ t₁⁻¹ s₂ t₂`

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  This is infrastructure for `thm:hull` in `non_mf_groups_exist.tex`
(around line 2121).

`junction_listing_of_filter` specialises `exists_junction_listing` to a pocket face set
`K : PocketFaceSet D eps X lo hi`, whose boundary cycle is
`firstSide ++ sourceArc⁻¹ ++ secondSide ++ targetArc`.  Take any predicate `p` for the kept darts.
Suppose the kept darts in cycle order form a nonempty walk, and the kept parts of the two arcs are
arcs `t₁'`, `t₂'`.  Then the kept darts are listed as `s₁ t₁'⁻¹ s₂ t₂'`, where

* the listing is a permutation of the kept darts (it is equal to them);
* `s₁`, `s₂` are walks of length at most `ε`;
* the three junctions meet at a vertex.

This is ingredient (2) of the rose planarity core
`GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement`, stated for pockets.
Everything here is unconditional.
-/

namespace GroupApproximation.Full.GL03C

universe u w v

open GroupApproximation.GGT.VanKampen GroupApproximation.GGT.VanKampen.Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}

/-- **Ingredient (2) of the rose planarity core, for a pocket face set** (Osin 9.7(b),
infrastructure for `thm:hull`, `non_mf_groups_exist.tex`).  If the darts of the pocket boundary
kept by `p` form a nonempty walk in cycle order, and the kept parts of the source and target arcs
are arcs `t₁'`, `t₂'`, then the kept darts are listed as `s₁ t₁'⁻¹ s₂ t₂'` with walks `s₁`, `s₂`
of length at most `ε` and three junctions meeting at a vertex. -/
theorem junction_listing_of_filter {D : GGT.RelGenSet G Lambda} {eps lo hi : ℕ}
    {X : DiscDiagram.{u, w, v} W} (K : PocketFaceSet D eps X lo hi)
    (p : X.toCombMap.Dart → Bool)
    {t₁' : CyclicArc (cellDarts X K.source)} {t₂' : CyclicArc (outerDarts X)}
    (hne : K.boundary.cycle.filter p ≠ [])
    (hchain : (K.boundary.cycle.filter p).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e)
    (hA : K.sourceArc.darts.filter (fun d => p (X.toCombMap.alpha d)) = t₁'.darts)
    (hB : K.targetArc.darts.filter p = t₂'.darts) :
    ∃ s₁ s₂ : List X.toCombMap.Dart,
      List.Perm (s₁ ++ invDarts X t₁'.darts ++ s₂ ++ t₂'.darts)
        (K.boundary.cycle.filter p) ∧
      s₁ ++ invDarts X t₁'.darts ++ s₂ ++ t₂'.darts ≠ [] ∧
      (s₁.IsChain fun d e =>
        X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
      (s₂.IsChain fun d e =>
        X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
      (∀ a ∈ s₁.getLast?, ∀ b ∈ (invDarts X t₁'.darts).head?,
        X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
      (∀ a ∈ (s₁ ++ invDarts X t₁'.darts).getLast?, ∀ b ∈ s₂.head?,
        X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
      (∀ a ∈ (s₁ ++ invDarts X t₁'.darts ++ s₂).getLast?, ∀ b ∈ t₂'.darts.head?,
        X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
      s₁.length ≤ eps ∧ s₂.length ≤ eps := by
  rw [K.decomposition] at hne hchain ⊢
  obtain ⟨s₁, s₂, heq, hs₁c, hs₂c, hj₁, hj₂, hj₃, hl₁, hl₂⟩ :=
    exists_junction_listing X
      (fun d e => X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) p
      K.firstSide K.secondSide K.sourceArc t₁' K.targetArc t₂' hA hB hchain
  have hne' : s₁ ++ invDarts X t₁'.darts ++ s₂ ++ t₂'.darts ≠ [] := by
    rw [heq]
    exact hne
  exact ⟨s₁, s₂, List.Perm.of_eq heq, hne', hs₁c, hs₂c, hj₁, hj₂, hj₃,
    hl₁.trans K.firstSide_length_le, hl₂.trans K.secondSide_length_le⟩

end GroupApproximation.Full.GL03C
