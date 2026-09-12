import GroupApproximation.KOne.AryRankNormalForm
import GroupApproximation.KOne.AryWindowProductClosure
import GroupApproximation.Meta.AxiomGuard

/-!
# Nilpotent tails die, at arbitrary arity

`KOne/NilpotentTailKill.lean` over a complete matrix family on an alphabet `ι`, for any
letter `i`: if `z` is balanced and `sᵢ z` is nilpotent, then any unit of value `1 + sᵢ z`
lies in the stably elementary subgroup.  Induction on the nilpotency index `D`: with
`r := tᵢ(sᵢz)^{D-1}` (pure degree `D-2`), factor `r = R·σ` over the balanced `R := r·τ`,
take a balanced pseudo-inverse `Ξ` of `R`, and set `e := τΞr`.  Then `e(sᵢz) = 0`, the
mover `1 - sᵢ(ze)` has square-zero tail, and it carries `z` to `z - ze` whose tail has
nilpotency index `D-1`.  The receptacle is `stableUnits` at every arity: the argument
uses only unipotents.
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)
variable {k : Type*} [Field k] [Algebra k A]

theorem left_mem_window (i : ι) : F.left i ∈ Submodule.span k (F.degreeMonomials 1 1) :=
  Submodule.subset_span ⟨[i], [], by simp, by simp, by simp⟩

theorem right_mem_window (i : ι) :
    F.right i ∈ Submodule.span k (F.degreeMonomials (-1) (-1)) :=
  Submodule.subset_span ⟨[], [i], by simp, by simp, by simp⟩

theorem one_mem_window : (1 : A) ∈ Submodule.span k (F.degreeMonomials 0 0) :=
  Submodule.subset_span ⟨[], [], by simp, by simp, by simp⟩

theorem wordT_replicate_mem_window (i : ι) (m : ℕ) :
    F.wordT (List.replicate m i) ∈
      Submodule.span k (F.degreeMonomials (-(m : ℤ)) (-(m : ℤ))) :=
  Submodule.subset_span ⟨[], List.replicate m i, by simp, by simp, by simp⟩

/-- Powers of a degree-one element sit in the matching window. -/
theorem pow_mem_window {x : A} (hx : x ∈ Submodule.span k (F.degreeMonomials 1 1))
    (m : ℕ) : x ^ m ∈ Submodule.span k (F.degreeMonomials (m : ℤ) (m : ℤ)) := by
  induction m with
  | zero =>
      rw [pow_zero]
      exact_mod_cast F.one_mem_window (k := k)
  | succ m ih =>
      rw [pow_succ]
      have := F.window_mul_mem_span ih hx
      refine F.span_degreeMonomials_mono ?_ ?_ this <;> push_cast <;> omega

/-- **Nilpotent tails die.**  If `z` is balanced and `(sᵢ z)^D = 0`, every unit of value
`1 + sᵢ z` lies in the stably elementary subgroup. -/
theorem nilpotent_tail_mem_stableUnits [Nontrivial A] (i : ι) (D : ℕ) :
    ∀ {z : A}, z ∈ Submodule.span k (F.degreeMonomials 0 0) →
    (F.left i * z) ^ D = 0 → ∀ u : Aˣ, (u : A) = 1 + F.left i * z →
    u ∈ stableUnits A := by
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro z hz hnil u hu
  rcases D with _ | _ | _ | D
  · rw [pow_zero] at hnil
    exact absurd hnil one_ne_zero
  · rw [pow_one] at hnil
    have hu1 : u = 1 := Units.ext (by rw [hu, hnil, add_zero, Units.val_one])
    rw [hu1]
    exact one_mem _
  · obtain ⟨n, hzn⟩ := F.span_degree_zero_le_levelSpan (k := k) hz
    refine F.square_zero_tail_mem_stableUnits i hzn ?_ u hu
    rw [show F.left i * z * (F.left i * z) = (F.left i * z) ^ 2 from by rw [pow_two], hnil]
  · have hts : F.right i * F.left i = 1 := by rw [F.orthogonal, if_pos rfl]
    set nn : A := F.left i * z with hnn
    set r : A := F.right i * nn ^ (D + 2) with hr
    set w : List ι := List.replicate (D + 1) i with hw
    set τ : A := F.wordT w with hτ
    set σ : A := F.wordS w with hσ
    have hτσ : τ * σ = 1 := F.wordT_mul_wordS_self w
    have hnwin : nn ∈ Submodule.span k (F.degreeMonomials 1 1) := by
      have := F.window_mul_mem_span (F.left_mem_window (k := k) i) hz
      refine F.span_degreeMonomials_mono ?_ ?_ this <;> omega
    have hrwin : r ∈ Submodule.span k
        (F.degreeMonomials ((D : ℤ) + 1) ((D : ℤ) + 1)) := by
      have hp := F.pow_mem_window hnwin (D + 2)
      have := F.window_mul_mem_span (F.right_mem_window (k := k) i) hp
      refine F.span_degreeMonomials_mono ?_ ?_ this <;> push_cast <;> omega
    have hτwin : τ ∈ Submodule.span k
        (F.degreeMonomials (-((D : ℤ) + 1)) (-((D : ℤ) + 1))) := by
      have := F.wordT_replicate_mem_window (k := k) i (D + 1)
      refine F.span_degreeMonomials_mono ?_ ?_ this <;> push_cast <;> omega
    set R : A := r * τ with hR
    have hRwin : R ∈ Submodule.span k (F.degreeMonomials 0 0) := by
      have := F.window_mul_mem_span hrwin hτwin
      refine F.span_degreeMonomials_mono ?_ ?_ this <;> omega
    have hRσ : R * σ = r := by rw [hR, mul_assoc, hτσ, mul_one]
    obtain ⟨nR, hRlvl⟩ := F.span_degree_zero_le_levelSpan (k := k) hRwin
    obtain ⟨Ξ, hΞlvl, hΞ⟩ := F.exists_balanced_pseudoInverse hRlvl
    have hΞwin : Ξ ∈ Submodule.span k (F.degreeMonomials 0 0) :=
      F.span_levelMonomialSet_le_degree (k := k) nR hΞlvl
    set e : A := τ * Ξ * r with he
    have hewin : e ∈ Submodule.span k (F.degreeMonomials 0 0) := by
      have h1 := F.window_mul_mem_span hτwin hΞwin
      have h2 := F.window_mul_mem_span h1 hrwin
      refine F.span_degreeMonomials_mono ?_ ?_ h2 <;> omega
    have hrn : r * nn = 0 := by
      rw [hr, mul_assoc, ← pow_succ, hnil, mul_zero]
    have hen : e * nn = 0 := by
      rw [he, mul_assoc, mul_assoc, hrn]
      noncomm_ring
    have hre' : r * e = r := by
      rw [he, show r * (τ * Ξ * r) = (r * τ) * Ξ * r from by noncomm_ring, ← hR, ← hRσ,
        show R * Ξ * (R * σ) = (R * Ξ * R) * σ from by noncomm_ring, hΞ]
    have hsqm : F.left i * (z * e) * (F.left i * (z * e)) = 0 := by
      rw [show F.left i * (z * e) * (F.left i * (z * e)) =
        F.left i * (z * (e * (F.left i * z)) * e) from by noncomm_ring, hen]
      noncomm_ring
    set m : Aˣ := ⟨1 - F.left i * (z * e), 1 + F.left i * (z * e),
      by
        calc (1 - F.left i * (z * e)) * (1 + F.left i * (z * e))
            = 1 - F.left i * (z * e) * (F.left i * (z * e)) := by noncomm_ring
          _ = 1 := by rw [hsqm, sub_zero],
      by
        calc (1 + F.left i * (z * e)) * (1 - F.left i * (z * e))
            = 1 - F.left i * (z * e) * (F.left i * (z * e)) := by noncomm_ring
          _ = 1 := by rw [hsqm, sub_zero]⟩ with hm
    have hzewin : z * e ∈ Submodule.span k (F.degreeMonomials 0 0) := by
      have := F.window_mul_mem_span hz hewin
      refine F.span_degreeMonomials_mono ?_ ?_ this <;> omega
    have hmmem : m ∈ stableUnits A := by
      obtain ⟨nze, hzelvl⟩ := F.span_degree_zero_le_levelSpan (k := k)
        (Submodule.neg_mem _ hzewin)
      refine F.square_zero_tail_mem_stableUnits i hzelvl ?_ m ?_
      · rw [show F.left i * -(z * e) * (F.left i * -(z * e)) =
          F.left i * (z * e) * (F.left i * (z * e)) from by noncomm_ring, hsqm]
      · show (1 : A) - F.left i * (z * e) = 1 + F.left i * -(z * e)
        noncomm_ring
    have hmu : ((m * u : Aˣ) : A) = 1 + F.left i * (z - z * e) := by
      show (1 - F.left i * (z * e)) * (u : A) = _
      rw [hu]
      have hcross : F.left i * (z * e) * (F.left i * z) = 0 := by
        rw [show F.left i * (z * e) * (F.left i * z) =
          F.left i * (z * (e * (F.left i * z))) from by noncomm_ring, hen]
        noncomm_ring
      calc (1 - F.left i * (z * e)) * (1 + F.left i * z)
          = 1 + F.left i * (z - z * e) - F.left i * (z * e) * (F.left i * z) := by
            noncomm_ring
        _ = 1 + F.left i * (z - z * e) := by rw [hcross]; noncomm_ring
    have hz'win : z - z * e ∈ Submodule.span k (F.degreeMonomials 0 0) :=
      Submodule.sub_mem _ hz hzewin
    have hp1n : F.left i * r = nn ^ (D + 2) := by
      rw [hr, show F.left i * (F.right i * nn ^ (D + 2)) =
        (F.left i * F.right i) * nn ^ (D + 2) from by noncomm_ring]
      have hpow : nn ^ (D + 2) = F.left i * (z * nn ^ (D + 1)) := by
        rw [show nn ^ (D + 2) = nn * nn ^ (D + 1) from by rw [← pow_succ'], hnn]
        noncomm_ring
      rw [hpow, show F.left i * F.right i * (F.left i * (z * nn ^ (D + 1))) =
        F.left i * (F.right i * F.left i) * (z * nn ^ (D + 1)) from by noncomm_ring, hts]
      noncomm_ring
    have hstep : ∀ j : ℕ, (F.left i * (z - z * e)) ^ (j + 1) =
        nn ^ (j + 1) - nn ^ (j + 1) * e := by
      intro j
      induction j with
      | zero =>
          rw [pow_one, pow_one, hnn]
          noncomm_ring
      | succ j ihj =>
          rw [pow_succ, ihj]
          have hexp : (nn ^ (j + 1) - nn ^ (j + 1) * e) * (F.left i * (z - z * e)) =
              nn ^ (j + 1) * nn - nn ^ (j + 1) * (nn * e) - nn ^ (j + 1) * (e * nn) +
                nn ^ (j + 1) * (e * nn) * e := by
            rw [hnn]
            noncomm_ring
          rw [hexp, hen]
          rw [show nn ^ (j + 1) * nn = nn ^ (j + 2) from by rw [← pow_succ]]
          noncomm_ring
    have hnil' : (F.left i * (z - z * e)) ^ (D + 2) = 0 := by
      rw [show D + 2 = (D + 1) + 1 from rfl, hstep (D + 1)]
      rw [show nn ^ (D + 1 + 1) = nn ^ (D + 2) from rfl]
      rw [← hp1n, mul_assoc, hre', sub_self]
    have hmumem := ih (D + 2) (by omega) hz'win hnil' (m * u) hmu
    have := mul_mem (inv_mem hmmem) hmumem
    rwa [inv_mul_cancel_left] at this

end CompleteMatrixFamily
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.pow_mem_window
#audit_axioms GroupApproximation.CompleteMatrixFamily.nilpotent_tail_mem_stableUnits
