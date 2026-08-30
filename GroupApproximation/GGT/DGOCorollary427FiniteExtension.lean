import GroupApproximation.GGT.GuessingGeodesicsCriterion
import GroupApproximation.GGT.OsinEnlargement

/-!
# The finite-alphabet part of DGO Corollary 4.27

Dahmani--Guirardel--Osin, Corollary 4.27 says that hyperbolic embeddedness is
unchanged when the relative base is changed by finitely many letters.  This
file isolates the direction used by Hull: adjoin one element and its inverse to
the base.

The hyperbolicity clause is proved here, rather than cited.  It is an immediate
application of Osin's proved Lemma 5.5: an old geodesic for either new letter
has bounded length, and old letters have length at most one.  Thus every old
geodesic joining the endpoints of a new edge has uniformly bounded diameter in
the enlarged metric.

Only local finiteness of the enlarged relative balls remains.  It is named as
`PairLocalFiniteness`; this is precisely the relative-metric content of
Corollary 4.27 for the one finite enlargement Hull uses.  Keeping that premise
separate prevents the hyperbolicity half of the citation from being charged to
the literature a second time.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

namespace RelGenSet

variable {G : Type u} [Group G] {Λ : Type w}

/-- Adjoin one element and its inverse to the relative base.  The peripheral
family is unchanged. -/
def adjoinPair (D : RelGenSet G Λ) (t : G) : RelGenSet G Λ where
  base := D.base ∪ {t, t⁻¹}
  fam := D.fam
  symmetricGenerating := by
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with (hx | hx) | hx
      · have hi := D.symmetricGenerating.inv_mem x (Or.inl hx)
        rcases hi with hi | hi
        · exact Or.inl (Or.inl hi)
        · exact Or.inr hi
      · rcases hx with rfl | rfl
        · exact Or.inl (Or.inr (Or.inr rfl))
        · exact Or.inl (Or.inr (Or.inl (inv_inv t)))
      · have hi := D.symmetricGenerating.inv_mem x (Or.inr hx)
        rcases hi with hi | hi
        · exact Or.inl (Or.inl hi)
        · exact Or.inr hi
    · refine eq_top_iff.mpr ?_
      rw [← D.symmetricGenerating.closure_eq]
      exact Subgroup.closure_mono fun x hx =>
        hx.elim (fun h => Or.inl (Or.inl h)) Or.inr

@[simp] theorem adjoinPair_base (D : RelGenSet G Λ) (t : G) :
    (D.adjoinPair t).base = D.base ∪ {t, t⁻¹} := rfl

@[simp] theorem adjoinPair_fam (D : RelGenSet G Λ) (t : G) :
    (D.adjoinPair t).fam = D.fam := rfl

theorem base_subset_adjoinPair (D : RelGenSet G Λ) (t : G) :
    D.base ⊆ (D.adjoinPair t).base := Set.subset_union_left

theorem alphabet_subset_adjoinPair (D : RelGenSet G Λ) (t : G) :
    D.alphabet.carrier ⊆ (D.adjoinPair t).alphabet.carrier := by
  exact OsinEnlargement.alphabet_mono (base_subset_adjoinPair D t) rfl

/-- The adjoined element is literally one base letter, rather than a word in
the old base. -/
theorem isLetter_base_adjoinPair (D : RelGenSet G Λ) (t : G) :
    (D.adjoinPair t).IsLetter (RelLetter.base t) := by
  exact Or.inr (Or.inl rfl)

/-- The inverse is adjoined simultaneously, as required by symmetry. -/
theorem isLetter_base_inv_adjoinPair (D : RelGenSet G Λ) (t : G) :
    (D.adjoinPair t).IsLetter (RelLetter.base t⁻¹) := by
  exact Or.inr (Or.inr rfl)

/-- The one-letter spelling supplied by the enlargement has the intended
value. -/
theorem listVal_single_base_adjoinPair (_D : RelGenSet G Λ) (t : G) :
    RelLetter.listVal ([RelLetter.base t] : List (RelLetter G Λ)) = t := by
  simp [RelLetter.listVal, RelLetter.val]

/-- Hull's relator uses `t⁻¹`.  After the pair enlargement its base arc is
the literal singleton spelling, with value `t⁻¹` and length one.  This is
the formal (W1)/(W4) spelling repair. -/
theorem singleton_inv_base_spelling_adjoinPair (D : RelGenSet G Λ) (t : G) :
    (∀ a ∈ ([t⁻¹] : List G),
      (D.adjoinPair t).IsLetter (RelLetter.base a)) ∧
      RelLetter.listVal
          (([t⁻¹] : List G).map (RelLetter.base : G → RelLetter G Λ)) = t⁻¹ ∧
        ([t⁻¹] : List G).length = 1 := by
  refine ⟨?_, ?_, rfl⟩
  · intro a ha
    simp only [List.mem_singleton] at ha
    subst a
    exact isLetter_base_inv_adjoinPair D t
  · simp [RelLetter.listVal, RelLetter.val]

/-- The base changes by at most the two displayed letters. -/
theorem finite_base_symmDiff_adjoinPair (D : RelGenSet G Λ) (t : G) :
    ((D.base \ (D.adjoinPair t).base) ∪
      ((D.adjoinPair t).base \ D.base)).Finite := by
  refine Set.Finite.union (Set.finite_empty.subset ?_)
    (((Set.finite_singleton t⁻¹).insert t).subset ?_)
  · intro x hx
    exact (hx.2 (base_subset_adjoinPair D t hx.1)).elim
  · rintro x ⟨hx, hnot⟩
    exact hx.resolve_left hnot

/-- The old word length of the two newly adjoined letters has a common
bound. -/
theorem exists_pair_wordNorm_bound (D : RelGenSet G Λ) (t : G) :
    ∃ M : ℕ, 1 ≤ M ∧ wordNorm D.alphabet.carrier t ≤ M ∧
      wordNorm D.alphabet.carrier t⁻¹ ≤ M := by
  exact ⟨1 + wordNorm D.alphabet.carrier t + wordNorm D.alphabet.carrier t⁻¹,
    by omega, by omega, by omega⟩

/-- **The hyperbolicity half of Corollary 4.27 for adjoining a pair.** -/
theorem exists_hyperbolic_adjoinPair (D : RelGenSet G Λ) (t : G) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (Cayley D.alphabet)) :
    ∃ δ' : ℝ, IsHyperbolicSpace δ' (Cayley (D.adjoinPair t).alphabet) := by
  obtain ⟨M, hM1, hMt, hMti⟩ := exists_pair_wordNorm_bound D t
  refine OsinEnlargement.osinLemma55 G D.alphabet (D.adjoinPair t).alphabet
    (alphabet_subset_adjoinPair D t) δ hδ M ?_
  intro b hb w hw hprod hlen i hi
  have hnorm : wordNorm D.alphabet.carrier b ≤ M := by
    rcases hb with (hb | hb) | hb
    · have hbOld : b ∈ D.alphabet.carrier := Or.inl hb
      exact (wordNorm_le_one_of_mem hbOld).trans hM1
    · rcases hb with rfl | rfl
      · exact hMt
      · exact hMti
    · have hbOld : b ∈ D.alphabet.carrier := Or.inr hb
      exact (wordNorm_le_one_of_mem hbOld).trans hM1
  have htake : ∀ x ∈ w.take i, x ∈ D.alphabet.carrier := by
    intro x hx
    exact hw x (List.take_subset i w hx)
  have hpre : wordNorm D.alphabet.carrier (w.take i).prod ≤ (w.take i).length :=
    wordNorm_le_length ⟨htake, rfl⟩
  rw [wordDist_one_left]
  calc
    wordNorm (D.adjoinPair t).alphabet.carrier (w.take i).prod
        ≤ wordNorm D.alphabet.carrier (w.take i).prod :=
      wordNorm_mono (alphabet_subset_adjoinPair D t)
        (wordLengths_nonempty D.alphabet.symmetricGenerating _)
    _ ≤ (w.take i).length := hpre
    _ ≤ w.length := by
      rw [List.length_take]
      exact min_le_right _ _
    _ = wordNorm D.alphabet.carrier b := by
      rw [hlen, wordDist_one_left]
    _ ≤ M := hnorm

/-- The sole remaining relative-metric premise in the one-pair enlargement
used by Hull. -/
def PairLocalFiniteness : Prop :=
  ∀ (G : Type u) [Group G] (Λ : Type w) (D : RelGenSet G Λ),
    D.IsHyperbolicallyEmbedded → ∀ t : G,
      ∀ (lam : Λ) (n : ℕ), ((D.adjoinPair t).relBall lam n).Finite

/-- Full Corollary 4.27 implies exactly the remaining one-pair local-finiteness
statement. -/
theorem pairLocalFiniteness_of_corollary427
    (h427 : DGOCorollary427.{u, w}) : PairLocalFiniteness.{u, w} := by
  intro G _ Λ D hemb t lam n
  have hemb' := (h427 G Λ D (D.adjoinPair t) rfl
    (finite_base_symmDiff_adjoinPair D t)).mp hemb
  exact hemb'.locallyFinite lam n

/-- The pair-local-finiteness content, together with the proved hyperbolicity
transport, gives hyperbolic embeddedness over the enlarged alphabet. -/
theorem isHyperbolicallyEmbedded_adjoinPair_of_localFiniteness
    (hloc : PairLocalFiniteness.{u, w}) (D : RelGenSet G Λ)
    (hemb : D.IsHyperbolicallyEmbedded) (t : G) :
    (D.adjoinPair t).IsHyperbolicallyEmbedded := by
  obtain ⟨δ, hδ⟩ := hemb.hyperbolic
  exact ⟨exists_hyperbolic_adjoinPair D t hδ, hloc G Λ D hemb t⟩

/-- DGO Corollary 4.27 itself immediately supplies the remaining one-pair
premise.  This theorem is the exact adapter used by the Hull lanes. -/
theorem isHyperbolicallyEmbedded_adjoinPair_of_corollary427
    (h427 : DGOCorollary427.{u, w}) (D : RelGenSet G Λ)
    (hemb : D.IsHyperbolicallyEmbedded) (t : G) :
    (D.adjoinPair t).IsHyperbolicallyEmbedded := by
  exact (h427 G Λ D (D.adjoinPair t) rfl
    (finite_base_symmDiff_adjoinPair D t)).mp hemb

end RelGenSet

end GGT
end GroupApproximation
