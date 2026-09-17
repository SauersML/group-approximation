import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.ConjRow
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.CommutatorCalculus
import GroupApproximation.Meta.AxiomGuard

/-!
# Padded centrality: `stab K₂(n, R)` is central in `St_{n+1}(R)` (lane sk-leavitt-03, endpoint)

Carto `sk-leavitt` lane 03 (Khanh Lemma 5.6), over an arbitrary unital ring `R`.

Let `k ∈ K₂(n, R)`, so `padMat k = 1`.  The conjugation formulas in `PaddedCentral.ConjCol`
and `PaddedCentral.ConjRow` show that `stab k` commutes with every
`x_{i,last}(a) = padCol (e_i(a))` and every `x_{last,j}(a) = padRow (e_j(a))`.  The remaining
generators are commutators, `x_{ij}(c) = ⁅x_{i,last}(c), x_{last,j}(1)⁆`, so
`LeavittFP.commute_commutatorElement_right` handles them.  `PresentedGroup.generated_by` then
puts all of `St_{n+1}(R)` in the centralizer of `stab k`.

## Truth check

The lane's hypothesis `3 ≤ n` is not needed: the argument works for every `n`.
`map_stab_K2_le_center` is the hypothesis-free form.  `stab_K2_le_center` is the lane's
signature, with its hypothesis unused.

The route is self-contained.  It does not use lane 02 (`RowColumn`), because the column and row
vectors here are local (`PaddedCentral.padCol` / `padRow`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open scoped commutatorElement
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open PaddedCentral

/-- For `k ∈ K₂(n, R)`, `stab k` commutes with every Steinberg root of `St_{n+1}(R)`. -/
theorem stab_commute_x_of_mem_K2 {R : Type*} [Ring R] {n : ℕ} {k : St n R}
    (hk : k ∈ K2 (Fin n) R) (p q : Fin (n + 1)) (hpq : p ≠ q) (c : R) :
    Commute (stab n R k) (x p q hpq c) := by
  rcases Fin.eq_castSucc_or_eq_last p with ⟨i, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last q with ⟨j, rfl⟩ | rfl
    · have hcm := x_commutator i.castSucc (Fin.last n) j.castSucc (Fin.castSucc_lt_last i).ne
        (Fin.castSucc_lt_last j).ne' hpq c 1
      rw [mul_one] at hcm
      rw [← hcm, ← padCol_single i c, ← padRow_single j 1]
      exact LeavittFP.commute_commutatorElement_right (stab_commute_padCol hk _)
        (stab_commute_padRow hk _)
    · rw [← padCol_single i c]
      exact stab_commute_padCol hk _
  · rcases Fin.eq_castSucc_or_eq_last q with ⟨j, rfl⟩ | rfl
    · rw [← padRow_single j c]
      exact stab_commute_padRow hk _
    · exact absurd rfl hpq

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stab_commute_x_of_mem_K2

/-- **Padded centrality, all ranks** (Khanh Lemma 5.6): `stab K₂(n, R) ≤ Z(St_{n+1}(R))`. -/
theorem map_stab_K2_le_center {R : Type*} [Ring R] {n : ℕ} :
    (K2 (Fin n) R).map (stab n R) ≤ Subgroup.center (St (n + 1) R) := by
  rintro _ ⟨k, hk, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer {stab n R k} := by
    refine PresentedGroup.generated_by _ _ ?_ g
    rintro ⟨p, q, hpq, c⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact stab_commute_x_of_mem_K2 hk p q hpq c
  exact (Subgroup.mem_centralizer_iff.mp hg (stab n R k) (Set.mem_singleton _)).symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.map_stab_K2_le_center

/-- **Lane sk-leavitt-03 endpoint** (Khanh Lemma 5.6), in the lane's signature.  The hypothesis
`3 ≤ n` is unused; see `map_stab_K2_le_center`. -/
theorem stab_K2_le_center {R : Type*} [Ring R] {n : ℕ} (_hn : 3 ≤ n) :
    (K2 (Fin n) R).map (stab n R) ≤ Subgroup.center (St (n + 1) R) :=
  map_stab_K2_le_center

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stab_K2_le_center

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
