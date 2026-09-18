import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AbsorbLobeStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AbsorbFaceSetProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-41: the target from one maximal absorption step

* `FourPieceWitness.absorbLobe_exists_max`: over a finite type, if some pair is basic then some
  basic pair is card-maximal.  It is obtained from `absorbFaceSet_iterate`, with "maximal" as the
  goal property.
* `FourPieceWitness.absorbLobe_not_insert`: a card-maximal `F` cannot absorb a new element `f`
  into any basic pair.
* `FourPieceWitness.absorbLobe_iterate`: Base, plus an Improve step that is only required at
  maximal pairs, gives a good pair or the escape.
* `FourPieceWitness.absorbLobe_noPlanarDegenStep`: `AbsorbLobeStatement` implies the target.
* `FourPieceWitness.absorbLobe_of_absorbFaceSet`, `absorbLobe_absorbFaceSet`,
  `absorbLobe_iff_absorbFaceSet`, `absorbLobe_iff_noPlanarDegenStep`: the equivalences.

## LOUD: EQUIVALENT to the target; Base NOT proved

See the docstring of `AbsorbLobeStatement.lean`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **A card-maximal basic pair exists** once some basic pair exists over a finite type. -/
theorem absorbLobe_exists_max {β : Type*} {γ : Type*} [Fintype β] {B : Finset β → γ → Prop}
    (h : ∃ F x, B F x) : ∃ F x, B F x ∧ ∀ F' x', B F' x' → F'.card ≤ F.card := by
  have hstep : ∀ (F : Finset β) (x : γ), B F x →
      ¬ (∀ F' x', B F' x' → F'.card ≤ F.card) →
      (∃ F' x', B F' x' ∧ (F.card < F'.card ∨ ∀ F'' x'', B F'' x'' → F''.card ≤ F'.card)) ∨
        False := by
    intro F _ _ hS
    refine Or.inl ?_
    by_contra hne
    apply hS
    intro F' x' hB'
    by_contra hlt
    exact hne ⟨F', x', hB', Or.inl (by omega)⟩
  rcases absorbFaceSet_iterate (β := β) (γ := γ) (B := B)
      (S := fun F _ => ∀ F' x', B F' x' → F'.card ≤ F.card) (R := False) (Or.inl h) hstep with
    hgood | hF
  · exact hgood
  · exact hF.elim

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbLobe_exists_max

/-- **A card-maximal set cannot absorb a new element** into any basic pair. -/
theorem absorbLobe_not_insert {β : Type*} {γ : Type*} [DecidableEq β]
    {B : Finset β → γ → Prop} {F : Finset β} (hmax : ∀ F' x', B F' x' → F'.card ≤ F.card)
    {f : β} (hf : f ∉ F) (x' : γ) : ¬ B (insert f F) x' := by
  intro hB
  have h1 := hmax _ x' hB
  rw [Finset.card_insert_of_notMem hf] at h1
  omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbLobe_not_insert

/-- **Iteration with Improve only at maximal pairs.**  One Improve call at a card-maximal basic
pair suffices: its card-strict disjunct is contradictory there. -/
theorem absorbLobe_iterate {β : Type*} {γ : Type*} [Fintype β]
    {B S : Finset β → γ → Prop} {R : Prop}
    (hbase : (∃ F x, B F x) ∨ R)
    (hstep : ∀ F x, B F x → ¬ S F x → (∀ F' x', B F' x' → F'.card ≤ F.card) →
      (∃ F' x', B F' x' ∧ (F.card < F'.card ∨ S F' x')) ∨ R) :
    (∃ F x, B F x ∧ S F x) ∨ R := by
  rcases hbase with hex | hR
  · obtain ⟨F, x, hB, hmax⟩ := absorbLobe_exists_max hex
    by_cases hS : S F x
    · exact Or.inl ⟨F, x, hB, hS⟩
    · rcases hstep F x hB hS hmax with ⟨F', x', hB', hlt | hS'⟩ | hR'
      · have hle := hmax F' x' hB'
        exfalso
        omega
      · exact Or.inl ⟨F', x', hB', hS'⟩
      · exact Or.inr hR'
  · exact Or.inr hR

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbLobe_iterate

/-- **The target from one maximal absorption step.**  See the module docstring. -/
theorem absorbLobe_noPlanarDegenStep (h : AbsorbLobeStatement.{u, w, v}) :
    NoPlanarDegenStepStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbj hdisj hlet hW hK1 hK2 G₁ hG₁ G₂ hG₂ hw
    hout hinE houtE C hC hCf hCa hCb hno hnc
  obtain ⟨hbase, himp⟩ := h D eps X a b K hij hai hbj hdisj hlet hW hK1 hK2 G₁ hG₁ G₂ hG₂ hw
    hout hinE houtE C hC hCf hCa hCb hno hnc
  rcases absorbLobe_iterate (β := X.toCombMap.Face) (γ := List X.toCombMap.Dart)
      (B := fun F ow => AbsorbFaceSetBasic a b K G₁ G₂ C.face F ow)
      (S := fun _ ow => AbsorbFaceSetStepGood G₁ G₂ ow)
      (R := AbsorbFaceSetBranchTwo i j C.face) hbase
      (fun F ow hB hS hmax =>
        himp F ow hB hS (absorbFaceSet_exposed_of_basic K hG₁ hG₂ hB hS) hmax) with
    ⟨F, ow, ⟨E, hc, hsub, hd, h1, h2, h3, h4⟩, s1, s2, s3, s4⟩ | hR
  · exact Or.inl ⟨F, ow, E, hc, hsub, hd, h1, h2, h3, h4, s1, s2, s3, s4⟩
  · exact Or.inr hR

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbLobe_noPlanarDegenStep

/-- **`AbsorbFaceSetStatement` implies `AbsorbLobeStatement`**: drop the maximality hypothesis. -/
theorem absorbLobe_of_absorbFaceSet (h : AbsorbFaceSetStatement.{u, w, v}) :
    AbsorbLobeStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbj hdisj hlet hW hK1 hK2 G₁ hG₁ G₂ hG₂ hw
    hout hinE houtE C hC hCf hCa hCb hno hnc
  obtain ⟨hbase, himp⟩ := h D eps X a b K hij hai hbj hdisj hlet hW hK1 hK2 G₁ hG₁ G₂ hG₂ hw
    hout hinE houtE C hC hCf hCa hCb hno hnc
  exact ⟨hbase, fun F ow hB hS hE _ => himp F ow hB hS hE⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbLobe_of_absorbFaceSet

/-- **`AbsorbLobeStatement` implies `AbsorbFaceSetStatement`**, through the target. -/
theorem absorbLobe_absorbFaceSet (h : AbsorbLobeStatement.{u, w, v}) :
    AbsorbFaceSetStatement.{u, w, v} :=
  absorbFaceSet_of_noPlanarDegenStep (absorbLobe_noPlanarDegenStep h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbLobe_absorbFaceSet

/-- **The maximal-step statement and the absorption iteration are equivalent.** -/
theorem absorbLobe_iff_absorbFaceSet :
    AbsorbLobeStatement.{u, w, v} ↔ AbsorbFaceSetStatement.{u, w, v} :=
  ⟨absorbLobe_absorbFaceSet, absorbLobe_of_absorbFaceSet⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbLobe_iff_absorbFaceSet

/-- **The maximal-step statement and the target are equivalent.** -/
theorem absorbLobe_iff_noPlanarDegenStep :
    AbsorbLobeStatement.{u, w, v} ↔ NoPlanarDegenStepStatement.{u, w, v} :=
  ⟨absorbLobe_noPlanarDegenStep,
    fun h => absorbLobe_of_absorbFaceSet (absorbFaceSet_of_noPlanarDegenStep h)⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbLobe_iff_noPlanarDegenStep

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
