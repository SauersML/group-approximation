import GroupApproximation.GGT.WPDHyperbolicallyEmbedded
import GroupApproximation.GGT.OsinPenetration
import GroupApproximation.Meta.AxiomGuard

/-!
# Dropping cyclic peripheral members (Osin's Lemma 8.2 at cyclic members)

Osin, *Small cancellations over relatively hyperbolic groups and embedding theorems*,
arXiv:math/0411039, Lemma 8.2 (a particular case of Theorem 2.40 of his memoir):

> Suppose that a group `G` is hyperbolic relative to a collection of subgroups
> `{H_λ}_{λ∈Λ} ∪ {S₁, …, S_m}`, where `S₁, …, S_m` are finitely generated and hyperbolic in the
> ordinary (non-relative) sense.  Then `G` is hyperbolic relative to `{H_λ}_{λ∈Λ}`.

In the proof of his Theorem 2.4 the dropped members are the images of the elementary subgroups
`E_G(h₁), E_G(h₂)`, which are cyclic.  In hyperbolically embedded form, and for a finite
collection, the same statement is Dahmani–Guirardel–Osin's Proposition 4.35 applied with the
trivial subcollections: `{H_λ} ↪_h (H_λ, ∅)` and `∅ ↪_h (⟨g_i⟩, {g_i^{±1}})`, which returns
`{H_λ} ↪_h (G, X ∪ {g_i^{±1}})`.

This is what the family form of Hull's Lemma 4.4 needs for its original-family conjunct: the
quotient keeps the joint family `{H_λ} ∪ {E_i}` hyperbolically embedded (small cancellation over
the joint collection, as Osin and Hull apply it), and the original family is recovered by
dropping the cyclic members over the finite enlargement `{g_i^{±1}}` of the base.

## What is here

* `removeCyclicPeripherals J g hg hbaseInv`: the relative generating set with base
  `J.base ∪ ⋃ i, {g i, (g i)⁻¹}` and family `lam ↦ J.fam (Sum.inl lam)`.
* `CyclicPeripheralRemovalStatement`: the statement above.
* Its local-finiteness half is **proved**: `removeCyclicPeripherals_relBall_subset` reads each
  adjoined base letter `g i^{±1}` as the component letter of `J.fam (Sum.inr i)`, so every relative
  ball of the dropped structure sits inside the corresponding relative ball of `J`.
* `CyclicPeripheralRemovalHyperbolicityStatement`: the one residue, hyperbolicity of the un-coned
  relative Cayley graph, and `cyclicPeripheralRemovalStatement_of_hyperbolicity`.
* Model test: with no cyclic members the residue holds outright
  (`removeCyclicPeripherals_isHyperbolicallyEmbedded_of_isEmpty`).
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

section Removal

variable {Q : Type u} [Group Q] {Lambda : Type w} {I : Type v}

/-- **Drop the cyclic members of a labelled peripheral family**, adjoining a generator of each
and its inverse to the base.  The inversion-closure of the source base is what keeps the new
alphabet symmetric: a base letter whose inverse was a component letter of a dropped member must
still have its inverse among the letters. -/
def removeCyclicPeripherals (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) : RelGenSet Q Lambda where
  base := J.base ∪ ⋃ i : I, ({g i, (g i)⁻¹} : Set Q)
  fam := fun lam => J.fam (Sum.inl lam)
  symmetricGenerating := by
    refine ⟨?_, ?_⟩
    · rintro x ((hx | hx) | hx)
      · exact Or.inl (Or.inl (hbaseInv x hx))
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        refine Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨i, ?_⟩))
        rcases hi with rfl | hi
        · exact Or.inr rfl
        · rw [Set.mem_singleton_iff] at hi
          subst hi
          exact Or.inl (inv_inv (g i))
      · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hx
        exact Or.inr (Set.mem_iUnion.mpr ⟨lam, (J.fam (Sum.inl lam)).inv_mem hlam⟩)
    · refine eq_top_iff.mpr ?_
      rw [← J.symmetricGenerating.closure_eq, Subgroup.closure_le]
      rintro x (hx | hx)
      · exact Subgroup.subset_closure (Or.inl (Or.inl hx))
      · obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
        cases s with
        | inl lam =>
            exact Subgroup.subset_closure (Or.inr (Set.mem_iUnion.mpr ⟨lam, hs⟩))
        | inr i =>
            have hs' : x ∈ Subgroup.zpowers (g i) := by
              rw [← hg i]
              exact hs
            obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs'
            have hgi : g i ∈ Subgroup.closure
                ((J.base ∪ ⋃ j : I, ({g j, (g j)⁻¹} : Set Q)) ∪
                  ⋃ lam : Lambda, ((J.fam (Sum.inl lam) : Subgroup Q) : Set Q)) :=
              Subgroup.subset_closure (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨i, Or.inl rfl⟩)))
            exact Subgroup.zpow_mem _ hgi n

/-- **A word of the dropped structure is a word of `J`**, of the same value and length, avoiding
the same component: adjoined base letters become component letters of the dropped members, and
original component letters keep their label. -/
theorem exists_jointWord_of_removeCyclicPeripherals (J : RelGenSet Q (Sum Lambda I))
    (g : I → Q) (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) (lam : Lambda) :
    ∀ (w : List (RelLetter Q Lambda)) (v : Q),
      (∀ a ∈ w, (removeCyclicPeripherals J g hg hbaseInv).IsLetter a) →
      AvoidsFrom (removeCyclicPeripherals J g hg hbaseInv).fam lam w v →
        ∃ w' : List (RelLetter Q (Sum Lambda I)),
          (∀ b ∈ w', J.IsLetter b) ∧ RelLetter.listVal w' = RelLetter.listVal w ∧
            AvoidsFrom J.fam (Sum.inl lam) w' v ∧ w'.length = w.length := by
  intro w
  induction w with
  | nil =>
      intro v _ _
      exact ⟨[], fun b hb => by simp at hb, rfl, trivial, rfl⟩
  | cons a t ih =>
      intro v hletters havoid
      obtain ⟨hhead, htail⟩ := havoid
      have ha : (removeCyclicPeripherals J g hg hbaseInv).IsLetter a := hletters a (by simp)
      obtain ⟨t', ht'letters, ht'val, ht'avoid, ht'len⟩ :=
        ih (v * a.val) (fun b hb => hletters b (List.mem_cons_of_mem a hb)) htail
      cases a with
      | base x =>
          by_cases hx : x ∈ J.base
          · refine ⟨RelLetter.base x :: t', ?_, ?_, ?_, ?_⟩
            · intro b hb
              rcases List.mem_cons.mp hb with rfl | hb
              · exact hx
              · exact ht'letters b hb
            · simp only [OsinComponents.listVal_cons, ht'val, RelLetter.val]
            · exact ⟨fun h => h.1, ht'avoid⟩
            · rw [List.length_cons, List.length_cons, ht'len]
          · have hx' : x ∈ ⋃ i : I, ({g i, (g i)⁻¹} : Set Q) := by
              rcases ha with hbase | hcyc
              · exact absurd hbase hx
              · exact hcyc
            obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx'
            have hmem : x ∈ J.fam (Sum.inr i) := by
              rw [hg i]
              rcases hi with rfl | hi
              · exact Subgroup.mem_zpowers _
              · rw [Set.mem_singleton_iff] at hi
                rw [hi]
                exact (Subgroup.zpowers (g i)).inv_mem (Subgroup.mem_zpowers _)
            refine ⟨RelLetter.comp (Sum.inr i) x :: t', ?_, ?_, ?_, ?_⟩
            · intro b hb
              rcases List.mem_cons.mp hb with rfl | hb
              · exact hmem
              · exact ht'letters b hb
            · simp only [OsinComponents.listVal_cons, ht'val, RelLetter.val]
            · refine ⟨?_, ht'avoid⟩
              rintro ⟨hcomp, -⟩
              exact Sum.inr_ne_inl hcomp
            · rw [List.length_cons, List.length_cons, ht'len]
      | comp mu h =>
          refine ⟨RelLetter.comp (Sum.inl mu) h :: t', ?_, ?_, ?_, ?_⟩
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · exact ha
            · exact ht'letters b hb
          · simp only [OsinComponents.listVal_cons, ht'val, RelLetter.val]
          · refine ⟨?_, ht'avoid⟩
            rintro ⟨hcomp, hv⟩
            exact hhead ⟨Sum.inl_injective hcomp, hv⟩
          · rw [List.length_cons, List.length_cons, ht'len]

/-- **The relative balls of the dropped structure sit inside those of `J`.** -/
theorem removeCyclicPeripherals_relBall_subset (J : RelGenSet Q (Sum Lambda I))
    (g : I → Q) (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) (lam : Lambda) (n : ℕ) :
    (removeCyclicPeripherals J g hg hbaseInv).relBall lam n ⊆ J.relBall (Sum.inl lam) n := by
  rintro h ⟨hmem, w, hletters, hval, havoid, hlen⟩
  obtain ⟨w', hletters', hval', havoid', hlen'⟩ :=
    exists_jointWord_of_removeCyclicPeripherals J g hg hbaseInv lam w 1 hletters havoid
  exact ⟨hmem, w', hletters', hval'.trans hval, havoid', hlen'.le.trans hlen⟩

/-- **Clause (b) of `↪_h` survives dropping the cyclic members.** -/
theorem removeCyclicPeripherals_locallyFinite (J : RelGenSet Q (Sum Lambda I))
    (g : I → Q) (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) (hJ : J.IsHyperbolicallyEmbedded)
    (lam : Lambda) (n : ℕ) :
    ((removeCyclicPeripherals J g hg hbaseInv).relBall lam n).Finite :=
  (hJ.locallyFinite (Sum.inl lam) n).subset
    (removeCyclicPeripherals_relBall_subset J g hg hbaseInv lam n)

/-- With no cyclic members, nothing is adjoined and nothing is dropped: the two alphabets have
the same letters. -/
theorem removeCyclicPeripherals_alphabet_carrier_of_isEmpty [IsEmpty I]
    (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) :
    (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier = J.alphabet.carrier := by
  ext x
  constructor
  · rintro ((hx | hx) | hx)
    · exact Or.inl hx
    · obtain ⟨i, -⟩ := Set.mem_iUnion.mp hx
      exact isEmptyElim i
    · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hx
      exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl lam, hlam⟩)
  · rintro (hx | hx)
    · exact Or.inl (Or.inl hx)
    · obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
      cases s with
      | inl lam => exact Or.inr (Set.mem_iUnion.mpr ⟨lam, hs⟩)
      | inr i => exact isEmptyElim i

/-- **Model test: with no cyclic members the dropped structure is hyperbolically embedded**, so
the hypotheses of the statement below are consistent with its conclusion and the residue is not
vacuous. -/
theorem removeCyclicPeripherals_isHyperbolicallyEmbedded_of_isEmpty [IsEmpty I]
    (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) (hJ : J.IsHyperbolicallyEmbedded) :
    (removeCyclicPeripherals J g hg hbaseInv).IsHyperbolicallyEmbedded := by
  have hcarrier := removeCyclicPeripherals_alphabet_carrier_of_isEmpty J g hg hbaseInv
  have halphabet :
      (removeCyclicPeripherals J g hg hbaseInv).alphabet = J.alphabet := by
    revert hcarrier
    generalize (removeCyclicPeripherals J g hg hbaseInv).alphabet = A
    generalize J.alphabet = B
    rcases A with ⟨cA, hA⟩
    rcases B with ⟨cB, hB⟩
    intro h
    have h' : cA = cB := h
    subst h'
    rfl
  refine ⟨?_, removeCyclicPeripherals_locallyFinite J g hg hbaseInv hJ⟩
  rw [halphabet]
  exact hJ.hyperbolic

end Removal

/-! ## The statement and its split -/

/-- **Osin's Lemma 8.2 at infinite cyclic members** (Osin, math/0411039, Lemma 8.2;
Dahmani–Guirardel–Osin, Proposition 4.35 with trivial subcollections), for a finite labelled
family: dropping finitely many infinite cyclic members over the finite enlargement of the base by
their generators keeps the rest hyperbolically embedded.  The members Osin drops are the
elementary subgroups `E_G(h₁), E_G(h₂)` of infinite-order elements, which is the case stated. -/
def CyclicPeripheralRemovalStatement.{uQ, uL, uI} : Prop :=
  ∀ {Q : Type uQ} [Group Q] {Lambda : Type uL} {I : Type uI} [Finite I]
    (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base),
    (∀ i : I, ¬ IsOfFinOrder (g i)) →
    J.IsHyperbolicallyEmbedded →
      (removeCyclicPeripherals J g hg hbaseInv).IsHyperbolicallyEmbedded

/-- **The residue: the un-coned relative Cayley graph is hyperbolic.**  Clause (b) is
`removeCyclicPeripherals_locallyFinite`. -/
def CyclicPeripheralRemovalHyperbolicityStatement.{uQ, uL, uI} : Prop :=
  ∀ {Q : Type uQ} [Group Q] {Lambda : Type uL} {I : Type uI} [Finite I]
    (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base),
    (∀ i : I, ¬ IsOfFinOrder (g i)) →
    J.IsHyperbolicallyEmbedded →
      ∃ δ : ℝ, IsHyperbolicSpace δ (Cayley (removeCyclicPeripherals J g hg hbaseInv).alphabet)

/-- **The statement splits into exactly its residue.** -/
theorem cyclicPeripheralRemovalStatement_of_hyperbolicity
    (h : CyclicPeripheralRemovalHyperbolicityStatement.{u, w, v}) :
    CyclicPeripheralRemovalStatement.{u, w, v} := by
  intro Q _ Lambda I _ J g hg hbaseInv hinf hJ
  exact ⟨h J g hg hbaseInv hinf hJ, removeCyclicPeripherals_locallyFinite J g hg hbaseInv hJ⟩

end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.exists_jointWord_of_removeCyclicPeripherals
#audit_axioms GroupApproximation.GGT.removeCyclicPeripherals_relBall_subset
#audit_axioms GroupApproximation.GGT.removeCyclicPeripherals_locallyFinite
#audit_axioms GroupApproximation.GGT.removeCyclicPeripherals_alphabet_carrier_of_isEmpty
#audit_axioms GroupApproximation.GGT.removeCyclicPeripherals_isHyperbolicallyEmbedded_of_isEmpty
#audit_axioms GroupApproximation.GGT.cyclicPeripheralRemovalStatement_of_hyperbolicity
