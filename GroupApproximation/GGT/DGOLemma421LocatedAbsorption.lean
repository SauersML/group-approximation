import GroupApproximation.GGT.DGOLemma421Proof
import GroupApproximation.GGT.DGOLemma421OccurrenceBounds
import GroupApproximation.GGT.DGOLemma421OrderedBridge

/-!
# Locating matches in the finite absorption certificate

The strengthened counting certificate retains the first selected rank and
the injection of unmatched sources into short-side slots. Consequently every
window of `M + 1` sources contains a match, with quantitative source positions.
-/

namespace GroupApproximation.GGT.OsinComponents

/-- If unmatched sources occupy distinct slots among `M` possibilities, every
window of `M + 1` sources contains a match. -/
theorem exists_match_in_window_of_short_injective
    {N M : ℕ} (Matched : Fin N → Prop) (short : Fin N → Fin M)
    (hinj : ∀ i j, ¬ Matched i → ¬ Matched j → short i = short j → i = j)
    (lo : ℕ) (hwindow : lo + M < N) :
    ∃ i : Fin N, lo ≤ i.val ∧ i.val ≤ lo + M ∧ Matched i := by
  classical
  by_contra hnone
  let index : Fin (M + 1) → Fin N := fun j => ⟨lo + j.val, by omega⟩
  have hbad : ∀ j, ¬ Matched (index j) := by
    intro j hmatch
    apply hnone
    exact ⟨index j, by change lo ≤ lo + j.val; omega,
      by change lo + j.val ≤ lo + M; omega, hmatch⟩
  have hinjective : Function.Injective (fun j => short (index j)) := by
    intro i j heq
    have hindex := hinj (index i) (index j) (hbad i) (hbad j) heq
    have hval := congrArg Fin.val hindex
    change lo + i.val = lo + j.val at hval
    apply Fin.ext
    omega
  have hcard := Fintype.card_le_of_injective _ hinjective
  simp only [Fintype.card_fin] at hcard
  omega

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- Source ranks in the original certificate advance exactly one at a time. -/
theorem DGO421FiniteAbsorptionCertificate.rank_formula
    {D : RelGenSet G Lambda} {P Q : List (RelLetter G Lambda)} {N M K : ℕ}
    (cert : DGO421FiniteAbsorptionCertificate D P Q N M K) (hN : 0 < N)
    (i : Fin N) : (cert.rank i).val = (cert.rank ⟨0, hN⟩).val + i.val := by
  have haux : ∀ k : ℕ, ∀ hk : k < N,
      (cert.rank ⟨k, hk⟩).val = (cert.rank ⟨0, hN⟩).val + k := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
      intro hk
      have hk' : k < N := by omega
      have hprev := ih hk'
      have hnext := cert.rank_succ ⟨k, hk'⟩ hk
      change (cert.rank ⟨k + 1, hk⟩).val = (cert.rank ⟨k, hk'⟩).val + 1 at hnext
      omega
  exact haux i.val i.isLt

/-- The located certificate bounds the position of each source in the word. -/
theorem DGO421LocatedAbsorptionCertificate.source_bounds
    {D : RelGenSet G Lambda} {P Q : List (RelLetter G Lambda)} {N M K : ℕ}
    (cert : DGO421LocatedAbsorptionCertificate D P Q N M K)
    (hW1P : WWord.IsWOne P) (i : Fin N) :
    i.val ≤ cert.source i ∧ cert.source i ≤ 2 * i.val + 3 := by
  have hN : 0 < N := by have := i.isLt; omega
  have hformula := cert.toDGO421FiniteAbsorptionCertificate.rank_formula hN i
  have hupper := cert.rank_le i
  have hpos := peripheralOccurrence_pos_bounds hW1P (cert.rank i)
  rw [cert.rank_pos] at hpos
  constructor <;> omega

/-- A match can be selected in any sufficiently long source window. -/
theorem DGO421LocatedAbsorptionCertificate.exists_match_in_window
    {D : RelGenSet G Lambda} {P Q : List (RelLetter G Lambda)} {N M K : ℕ}
    (cert : DGO421LocatedAbsorptionCertificate D P Q N M K)
    (lo : ℕ) (hwindow : lo + M < N) :
    ∃ i : Fin N, lo ≤ i.val ∧ i.val ≤ lo + M ∧ cert.matched i :=
  exists_match_in_window_of_short_injective cert.matched cert.short cert.short_injective lo hwindow

/-- Every match in the counting certificate has a target rank and a coset
identity at the two original path basepoints. -/
theorem DGO421FiniteAbsorptionCertificate.matched_rank
    {D : RelGenSet G Lambda} {P Q : List (RelLetter G Lambda)} {N M K : ℕ}
    (cert : DGO421FiniteAbsorptionCertificate D P Q N M K) {vp vq : G}
    (hpre : cert.pre = vq⁻¹ * vp) (hletQ : ∀ letter ∈ Q, D.IsLetter letter)
    (i : Fin N) (hi : cert.matched i) :
    ∃ a : Fin (peripheralPositions Q).card,
      (peripheralOccurrence Q a).label = (peripheralOccurrence P (cert.rank i)).label ∧
      (vertex vp P (peripheralOccurrence P (cert.rank i)).pos)⁻¹ *
        vertex vq Q (peripheralOccurrence Q a).pos ∈ D.fam (peripheralOccurrence P (cert.rank i)).label := by
  obtain ⟨j, _, _, ⟨start, hcomp⟩, h, hmem, heq⟩ := cert.matched_spec i hi
  obtain ⟨a, hapos, halabel⟩ := exists_peripheralOccurrence_eq_of_isCompStart ⟨j, hcomp⟩
  have heq' : vertex vp P (cert.source i) * h = vertex vq Q j := by
    have hh := congrArg (fun z : G => vq * z) heq
    rw [hpre] at hh
    simp only [vertex_eq_mul_listVal_take, one_mul] at hh ⊢
    convert hh using 1
    group
  have hend : (vertex vp P (cert.source i))⁻¹ * vertex vq Q j ∈ D.fam (cert.label i) := by
    rw [← heq', inv_mul_cancel_left]
    exact hmem
  have hstart := cosetMatch_start_of_cosetMatch_end hletQ hcomp hend
  refine ⟨a, ?_, ?_⟩
  · rw [cert.rank_label]
    exact halabel
  · rw [cert.rank_label, cert.rank_pos, hapos]
    exact hstart

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.dgoLemma421b_locatedAbsorption_of_uniform414
#audit_axioms GroupApproximation.GGT.OsinComponents.exists_match_in_window_of_short_injective
#audit_axioms GroupApproximation.GGT.OsinComponents.DGO421FiniteAbsorptionCertificate.rank_formula
#audit_axioms GroupApproximation.GGT.OsinComponents.DGO421LocatedAbsorptionCertificate.source_bounds
#audit_axioms GroupApproximation.GGT.OsinComponents.DGO421LocatedAbsorptionCertificate.exists_match_in_window
#audit_axioms GroupApproximation.GGT.OsinComponents.DGO421FiniteAbsorptionCertificate.matched_rank
