import GroupApproximation.Matching.MaximalCutRepair
import GroupApproximation.Matching.CompletionGraphEditing
import GroupApproximation.Matching.DirectedCoarea
import GroupApproximation.Kun.KunGeneratorGraph
import GroupApproximation.Kun.KunBoundary

/-!
# Exact directed expansion on a retained component

`CentralizerNormalizationImprove.ComponentFamily` asks for an exact directed
Cheeger bound on the labels of every component.  Completed component labels
only expand at a scale: a completion may fix a point under every label.  This
module removes that obstruction on one finite model.

If the generator graph of `act` satisfies an additive Cheeger inequality with
error `E`, remove the maximum sparse cut of `MaximalCutRepair`.  Every
completion of the labels on the retained set that agrees with `act` wherever
`act` stays inside has the directed Cheeger bound `c / |T|` on `T.image`.  The
removed set has at most `E / (γ - c)` points.

* `boundaryCard_generatorGraph_le_card_mul_directedBoundary`: at most `|T|`
  generator occurrences share one directed boundary arc.
* `nearHalf_of_removed_bound`: the near-half inequality of the repair from a
  bound on the removed set.
* `retained_completion_directedCheeger`: the directed Cheeger bound.
* `additiveCheeger_of_edit`: the additive inequality from an edited expander.
-/

namespace GroupApproximation
namespace RetainedComponentExpansion

open scoped BigOperators

/-- The retained vertices of the maximum sparse cut repair. -/
noncomputable def retainedSet {G : Type} [Group G] (Y : FiniteModel) (T : Finset G)
    (act : G → Equiv.Perm Y) (c : ℝ) : Finset Y :=
  MaximalCutRepair.retained (generatorGraph Y T act) c

/-- The retained vertices as a finite model. -/
noncomputable abbrev retainedModel {G : Type} [Group G] (Y : FiniteModel) (T : Finset G)
    (act : G → Equiv.Perm Y) (c : ℝ) : FiniteModel :=
  { carrier := retainedSet Y T act c
    fintype := inferInstance
    decidableEq := inferInstance }

/-- At most `|T|` generator occurrences give the same directed boundary arc. -/
theorem boundaryCard_generatorGraph_le_card_mul_directedBoundary
    {G : Type} [Group G] (Y : FiniteModel) (T : Finset G)
    (act : G → Equiv.Perm Y) (U : Finset Y) :
    (generatorGraph Y T act).boundaryCard U ≤
      T.card * (AlmostAutomorphism.directedBoundary Y (T.image act) U).card := by
  classical
  unfold FiniteMultiGraph.boundaryCard
  refine Finset.card_le_mul_card_image_of_maps_to
    (f := fun e : (generatorGraph Y T act).edge ↦
      ((act e.1.1.1, e.1.2) : AlmostAutomorphism.Arc Y)) ?_ T.card ?_
  · intro e he
    have hcut := (Finset.mem_filter.mp he).2
    change (e.1.2 ∈ U ∧ act e.1.1.1 e.1.2 ∉ U) ∨
      (act e.1.1.1 e.1.2 ∈ U ∧ e.1.2 ∉ U) at hcut
    refine (AlmostAutomorphism.mem_directedBoundary Y (T.image act) U
      (act e.1.1.1, e.1.2)).mpr ⟨Finset.mem_image.mpr ⟨e.1.1.1, e.1.1.2, rfl⟩, ?_⟩
    rcases hcut with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2, h.1⟩
  · intro b _
    have hT : (Finset.univ : Finset T).card = T.card := by
      rw [Finset.card_univ, Fintype.card_coe]
    rw [← hT]
    apply Finset.card_le_card_of_injOn (fun e : (generatorGraph Y T act).edge ↦ e.1.1)
    · intro e _
      exact Finset.mem_univ _
    · intro e he f hf hef
      have he' := (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
      have hf' := (Finset.mem_filter.mp (Finset.mem_coe.mp hf)).2
      have hx : e.1.2 = f.1.2 := congrArg Prod.snd (he'.trans hf'.symm)
      have ht : e.1.1 = f.1.1 := hef
      apply Subtype.ext
      exact Prod.ext ht hx

/-- The degree bound for generator-graph boundaries. -/
theorem generatorGraph_boundary_degree {G : Type} [Group G] (Y : FiniteModel)
    (T : Finset G) (act : G → Equiv.Perm Y) (U : Finset Y) :
    ((generatorGraph Y T act).boundaryCard U : ℝ) ≤ (2 * T.card : ℕ) * U.card := by
  rw [KunGeneratorGraph.boundaryCard_generatorGraph]
  exact_mod_cast KazhdanGNS.generatorCutSize_le_two_mul_card Y act T U

/-- The near-half inequality of `MaximalCutRepair.induce_retained_hasCheegerLowerBound`
from the bound `k b ≤ E` on the removed set. -/
theorem nearHalf_of_removed_bound {k E d b N : ℝ} (hk : 0 < k) (hd : 0 ≤ d)
    (hb : k * b ≤ E) (hsmall : 4 * E * k + 2 * d * E ≤ k * k * N) :
    2 * (E + d * b) ≤ k * (N - 2 * b) := by
  have hdb : d * (k * b) ≤ d * E := mul_le_mul_of_nonneg_left hb hd
  have hkb : k * (k * b) ≤ k * E := mul_le_mul_of_nonneg_left hb hk.le
  have hmul : k * (2 * (E + d * b)) ≤ k * (k * (N - 2 * b)) := by
    nlinarith [hdb, hkb, hsmall]
  exact le_of_mul_le_mul_left hmul hk

/-- The removed set is small. -/
theorem sparseCut_card_mul_le {G : Type} [Group G] (Y : FiniteModel) (T : Finset G)
    (act : G → Equiv.Perm Y) {γ c E : ℝ} (hE : 0 ≤ E)
    (hadd : ∀ U : Finset Y, U.Nonempty → 2 * U.card ≤ Fintype.card Y →
      γ * (U.card : ℝ) ≤ ((generatorGraph Y T act).boundaryCard U : ℝ) + E) :
    (γ - c) * ((MaximalCutRepair.sparseCut (generatorGraph Y T act) c).card : ℝ) ≤ E :=
  MaximalCutRepair.sparseCut_card_bound (generatorGraph Y T act) (γ := γ) (c := c)
    (E := E) hE (fun U hU hhalf ↦ hadd U hU hhalf)

/-- The retained set and the removed cut partition the model. -/
theorem card_retainedSet_add_sparseCut {G : Type} [Group G] (Y : FiniteModel)
    (T : Finset G) (act : G → Equiv.Perm Y) (c : ℝ) :
    (retainedSet Y T act c).card +
        (MaximalCutRepair.sparseCut (generatorGraph Y T act) c).card =
      Fintype.card Y := by
  have h : (retainedSet Y T act c).card =
      Fintype.card Y - (MaximalCutRepair.sparseCut (generatorGraph Y T act) c).card :=
    MaximalCutRepair.retained_card (generatorGraph Y T act) c
  have hle : (MaximalCutRepair.sparseCut (generatorGraph Y T act) c).card ≤
      Fintype.card Y := Finset.card_le_univ _
  omega

/-- **Retained expansion.**  After removing the maximum sparse cut, every
completion of the labels on the retained set that agrees with `act` on internal
values has the exact directed Cheeger bound `c / |T|`. -/
theorem retained_completion_directedCheeger
    {G : Type} [Group G] (Y : FiniteModel) (T : Finset G) (hT : T.Nonempty)
    (act : G → Equiv.Perm Y) {γ c E : ℝ} (hc : 0 < c) (hgap : c < γ) (hE : 0 ≤ E)
    (hadd : ∀ U : Finset Y, U.Nonempty → 2 * U.card ≤ Fintype.card Y →
      γ * (U.card : ℝ) ≤ ((generatorGraph Y T act).boundaryCard U : ℝ) + E)
    (hsmall : 4 * E * (γ - c) + 2 * ((2 * T.card : ℕ) : ℝ) * E ≤
      (γ - c) * (γ - c) * (Fintype.card Y : ℝ))
    (completed : G → Equiv.Perm (retainedSet Y T act c))
    (hagree : ∀ (t : T) (x : retainedSet Y T act c),
      act t.1 (x : Y) ∈ retainedSet Y T act c →
        (completed t.1 x : Y) = act t.1 x) :
    DirectedCoarea.HasCheegerLowerBound (retainedModel Y T act c)
      (T.image completed) (c / T.card) := by
  classical
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have hbound : (γ - c) *
      ((MaximalCutRepair.sparseCut (generatorGraph Y T act) c).card : ℝ) ≤ E :=
    sparseCut_card_mul_le Y T act hE hadd
  have hnear : 2 * (E + ((2 * T.card : ℕ) : ℝ) *
        ((MaximalCutRepair.sparseCut (generatorGraph Y T act) c).card : ℝ)) ≤
      (γ - c) * ((Fintype.card (generatorGraph Y T act).vertex : ℝ) -
        2 * ((MaximalCutRepair.sparseCut (generatorGraph Y T act) c).card : ℝ)) :=
    nearHalf_of_removed_bound (sub_pos.mpr hgap) (by positivity) hbound hsmall
  have hind : ((generatorGraph Y T act).induce
      (retainedSet Y T act c)).HasCheegerLowerBound c :=
    MaximalCutRepair.induce_retained_hasCheegerLowerBound (generatorGraph Y T act)
      hc hgap (fun U hU hhalf ↦ hadd U hU hhalf)
      (generatorGraph_boundary_degree Y T act _) hnear
  refine ⟨div_pos hc hTpos, ?_⟩
  intro V hV hhalf
  have hcut : c * (V.card : ℝ) ≤
      (((generatorGraph Y T act).induce (retainedSet Y T act c)).boundaryCard V : ℝ) :=
    hind.2 V hV hhalf
  have hcomp := CompletionGraphEditing.induce_boundaryCard_le_completed
    (retainedSet Y T act c) T act completed hagree V
  have hmult := boundaryCard_generatorGraph_le_card_mul_directedBoundary
    (retainedModel Y T act c) T completed V
  have hnat : ((generatorGraph Y T act).induce (retainedSet Y T act c)).boundaryCard V ≤
      T.card * (AlmostAutomorphism.directedBoundary (retainedModel Y T act c)
        (T.image completed) V).card :=
    hcomp.trans hmult
  have hreal :
      (((generatorGraph Y T act).induce (retainedSet Y T act c)).boundaryCard V : ℝ) ≤
        (T.card : ℝ) * ((AlmostAutomorphism.directedBoundary (retainedModel Y T act c)
          (T.image completed) V).card : ℝ) := by
    exact_mod_cast hnat
  rw [div_mul_eq_mul_div, div_le_iff₀ hTpos]
  exact (hcut.trans hreal).trans_eq (mul_comm _ _)

/-- The additive Cheeger inequality from an edited expander. -/
theorem additiveCheeger_of_edit {G : Type} [Group G] (Y : FiniteModel) (T : Finset G)
    (act : G → Equiv.Perm Y) (Z : FiniteMultiGraph)
    (e : (generatorGraph Y T act).vertex ≃ Z.vertex) {γ B : ℝ}
    (hZ : Z.HasCheegerLowerBound γ)
    (hB : ((generatorGraph Y T act).editDistance Z e : ℝ) ≤ B) :
    ∀ U : Finset Y, U.Nonempty → 2 * U.card ≤ Fintype.card Y →
      γ / 2 * (U.card : ℝ) ≤ ((generatorGraph Y T act).boundaryCard U : ℝ) + B / 2 := by
  intro U hU hhalf
  have h : γ / 2 * (U.card : ℝ) ≤ ((generatorGraph Y T act).boundaryCard U : ℝ) +
      ((generatorGraph Y T act).editDistance Z e : ℝ) / 2 :=
    MaximalCutRepair.additiveCheeger_of_editDistance (generatorGraph Y T act) Z e hZ
      U hU hhalf
  linarith

end RetainedComponentExpansion
end GroupApproximation
