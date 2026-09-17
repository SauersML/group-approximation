import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SoficPestov.Definition

/-!
# Corpus soficity gives Pestov's normalization

tex l.105–109 (sofic groups "keep nontrivial elements uniformly far from~$1$~\cite{Pestov}").

Route.  A corpus model `M` for the test set `insert 1 F` at tolerance `δ = ε / 8` is transported to
`Fin (card M)` by `Fintype.equivFin` (`hammingDistance_permCongr`, `permCongr_mul`).  Pestov asks
for `φ 1 = 1`, so the model value at `1` is replaced by the identity.  That costs at most `δ` per
replaced value: `d(ψ 1, 1) = d(ψ 1, ψ 1 * ψ 1) ≤ δ` by left invariance.  The defect becomes
`≤ 4δ < ε` and the separation from `1` becomes `≥ 1 - 3δ > 1 - ε`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SkRows
namespace SoficPestov

/-- Normalizing a permutation model at the identity.  If `ψ` has defect `≤ δ` and separation
`≥ 1 - δ` on `insert 1 F`, then some `φ` with `φ 1 = 1` has defect `≤ 4δ` on `F` and keeps
nontrivial elements of `F` at distance `≥ 1 - 3δ` from `1`. -/
theorem exists_normalized_model {G : Type*} [Group G] [DecidableEq G] (Y : FiniteModel)
    (ψ : G → Equiv.Perm Y) (F : Finset G) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmul : ∀ g ∈ insert (1 : G) F, ∀ h ∈ insert (1 : G) F,
      hammingDistance Y (ψ (g * h)) (ψ g * ψ h) ≤ δ)
    (hsep : ∀ g ∈ insert (1 : G) F, ∀ h ∈ insert (1 : G) F, g ≠ h →
      1 - δ ≤ hammingDistance Y (ψ g) (ψ h)) :
    ∃ φ : G → Equiv.Perm Y, φ 1 = 1 ∧
      (∀ g ∈ F, ∀ h ∈ F, hammingDistance Y (φ (g * h)) (φ g * φ h) ≤ 4 * δ) ∧
      ∀ g ∈ F, g ≠ 1 → 1 - 3 * δ ≤ hammingDistance Y (φ g) 1 := by
  have h1 : (1 : G) ∈ insert (1 : G) F := Finset.mem_insert_self _ _
  have hF : ∀ g ∈ F, g ∈ insert (1 : G) F := fun g hg => Finset.mem_insert_of_mem hg
  have hone : hammingDistance Y (ψ 1) 1 ≤ δ := by
    have hm := hmul 1 h1 1 h1
    rw [one_mul] at hm
    have hinv := hammingDistance_left_invariant Y (ψ 1) 1 (ψ 1)
    rw [mul_one] at hinv
    rw [hammingDistance_comm, ← hinv]
    exact hm
  have hclose : ∀ g : G, hammingDistance Y (if g = 1 then 1 else ψ g) (ψ g) ≤ δ := by
    intro g
    by_cases hg : g = 1
    · subst hg
      rw [if_pos rfl, hammingDistance_comm]
      exact hone
    · rw [if_neg hg, hammingDistance_self]
      exact hδ
  obtain ⟨φ, hφ1, hφψ⟩ : ∃ φ : G → Equiv.Perm Y,
      φ 1 = 1 ∧ ∀ g, hammingDistance Y (φ g) (ψ g) ≤ δ :=
    ⟨fun g => if g = 1 then 1 else ψ g, by simp, hclose⟩
  refine ⟨φ, hφ1, ?_, ?_⟩
  · intro g hg h hh
    have e1 := hφψ (g * h)
    have e2 := hmul g (hF g hg) h (hF h hh)
    have e3 : hammingDistance Y (ψ g * ψ h) (φ g * ψ h) ≤ δ := by
      rw [hammingDistance_right_invariant, hammingDistance_comm]
      exact hφψ g
    have e4 : hammingDistance Y (φ g * ψ h) (φ g * φ h) ≤ δ := by
      rw [hammingDistance_left_invariant, hammingDistance_comm]
      exact hφψ h
    have t1 := hammingDistance_triangle Y (φ (g * h)) (ψ (g * h)) (φ g * φ h)
    have t2 := hammingDistance_triangle Y (ψ (g * h)) (ψ g * ψ h) (φ g * φ h)
    have t3 := hammingDistance_triangle Y (ψ g * ψ h) (φ g * ψ h) (φ g * φ h)
    linarith
  · intro g hg hg1
    have s1 := hsep g (hF g hg) 1 h1 hg1
    have t1 := hammingDistance_triangle Y (ψ g) (φ g) (ψ 1)
    have t2 := hammingDistance_triangle Y (φ g) 1 (ψ 1)
    have c1 : hammingDistance Y (ψ g) (φ g) ≤ δ := by
      rw [hammingDistance_comm]
      exact hφψ g
    have c2 : hammingDistance Y 1 (ψ 1) ≤ δ := by
      rw [hammingDistance_comm]
      exact hone
    linarith

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SoficPestov.exists_normalized_model

/-- **Corpus soficity implies soficity in Pestov's normalization.** -/
theorem isSoficPestov_of_isSofic {G : Type*} [Group G] (hG : IsSofic G) : IsSoficPestov G := by
  classical
  intro F ε hε
  obtain ⟨M⟩ := hG (insert 1 F) (ε / 8) (by positivity)
  have e : M.carrier ≃ (finModel (Fintype.card M.carrier)).carrier :=
    Fintype.equivFin M.carrier
  obtain ⟨φ, hφ1, hφmul, hφsep⟩ := exists_normalized_model
    (finModel (Fintype.card M.carrier)) (fun g => e.permCongr (M.map g)) F
    (δ := ε / 8) (by positivity)
    (fun g hg h hh => by
      simp only [← permCongr_mul, hammingDistance_permCongr]
      exact M.multiplicative g hg h hh)
    (fun g hg h hh hgh => by
      simp only [hammingDistance_permCongr]
      exact M.separated g hg h hh hgh)
  refine ⟨Fintype.card M.carrier, φ, fun g hg h hh => ?_, hφ1, fun g hg hg1 => ?_⟩
  · exact (pestovHammingDist_eq_hammingDistance (φ (g * h)) (φ g * φ h)).trans_lt
      (lt_of_le_of_lt (hφmul g hg h hh) (by linarith))
  · exact (lt_of_lt_of_le (by linarith) (hφsep g hg hg1)).trans_eq
      (pestovHammingDist_eq_hammingDistance (φ g) 1).symm

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SoficPestov.isSoficPestov_of_isSofic

end SoficPestov
end SkRows
end SimpleKazhdanSofic
end GroupApproximation
