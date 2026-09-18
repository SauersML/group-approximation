import GroupApproximation.KOne.RankNElimination
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin input, part 2: Euclidean elimination in one row

Lane `bh-met-23`.  `KOne/RankNElimination.lean` runs Gaussian elimination over rings in which
every nonzero element is invertible on both sides; the only place that hypothesis enters is
`exists_diag_one`, which plants a literal `1` on the diagonal.  Over a ring with a
*well-founded division with remainder* (`HasWellFoundedDivision`: Euclidean domains, `ℤ[1/m]`)
we plant that `1` by the Euclidean algorithm instead:

* `suslin_exists_kill_entry`: four column moves supported on `{t, j}` replace the `(t, j)`
  entry `s` by the remainder `A t t - s q`, so well-founded induction makes it `0` without
  changing the other entries of row `t`;
* `suslin_exists_row_killed`: doing this for every column kills row `t` off the diagonal;
* `suslin_exists_diag_one`: then `A t t` is a unit (its inverse is `(A⁻¹) t t`), and two moves
  through a second index `k` turn it into `1`.

All moves avoid the already cleared index set `S`, so the `ClearedOn` invariant survives.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open RankNElimination

/-- A **well-founded division with remainder**: a well-founded relation `r` such that every
`a` can be divided by every nonzero `b` with a remainder `a - b q` that is `r`-smaller than `b`.
Every Euclidean domain has one; so does every subsingleton ring (vacuously). -/
def HasWellFoundedDivision (R : Type*) [CommRing R] : Prop :=
  ∃ r : R → R → Prop, WellFounded r ∧ ∀ a b : R, b ≠ 0 → ∃ q : R, r (a - b * q) b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.HasWellFoundedDivision

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- One column move `A ↦ A · x_{ik}(a)` with `i, k ∉ S`, with its effect on the entries. -/
theorem suslin_exists_step (A : (Matrix ι ι R)ˣ) (S : Finset ι) (hA : ClearedOn S A)
    {i k : ι} (hik : i ≠ k) (hi : i ∉ S) (hk : k ∉ S) (a : R) :
    ∃ B : (Matrix ι ι R)ˣ, Reaches A B ∧ ClearedOn S B ∧
      ∀ r c : ι, (B : Matrix ι ι R) r c =
        if c = k then (A : Matrix ι ι R) r k + (A : Matrix ι ι R) r i * a
        else (A : Matrix ι ι R) r c :=
  ⟨A * elementaryUnit i k hik a, Reaches.right (elementaryUnit_mem i k hik a),
    hA.mul (elementaryUnit_clearedOn S hik hi hk a),
    fun r c ↦ by rw [Units.val_mul, mul_elementaryUnit_apply]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslin_exists_step

/-- **Killing one entry by the Euclidean algorithm.**  For `t ≠ j` outside the cleared set,
elementary moves make the `(t, j)` entry `0` and leave the other entries of row `t` (away from
columns `t` and `j`) unchanged. -/
theorem suslin_exists_kill_entry (hR : HasWellFoundedDivision R) (S : Finset ι) {t j : ι}
    (ht : t ∉ S) (hj : j ∉ S) (htj : t ≠ j) (A : (Matrix ι ι R)ˣ) (hA : ClearedOn S A) :
    ∃ M : (Matrix ι ι R)ˣ, Reaches A M ∧ ClearedOn S M ∧ (M : Matrix ι ι R) t j = 0 ∧
      ∀ c : ι, c ≠ t → c ≠ j → (M : Matrix ι ι R) t c = (A : Matrix ι ι R) t c := by
  obtain ⟨rel, hwf, hdiv⟩ := hR
  have hjt : j ≠ t := Ne.symm htj
  suffices H : ∀ s : R, ∀ A : (Matrix ι ι R)ˣ, ClearedOn S A → (A : Matrix ι ι R) t j = s →
      ∃ M : (Matrix ι ι R)ˣ, Reaches A M ∧ ClearedOn S M ∧ (M : Matrix ι ι R) t j = 0 ∧
        ∀ c : ι, c ≠ t → c ≠ j → (M : Matrix ι ι R) t c = (A : Matrix ι ι R) t c from
    H _ A hA rfl
  intro s
  induction s using hwf.induction with
  | _ s IH =>
    intro A hA hAs
    by_cases hs : s = 0
    · exact ⟨A, Reaches.refl A, hA, hAs.trans hs, fun _ _ _ ↦ rfl⟩
    obtain ⟨q, hq⟩ := hdiv ((A : Matrix ι ι R) t t) s hs
    obtain ⟨B1, h1r, h1c, h1⟩ := suslin_exists_step A S hA hjt hj ht (-q)
    obtain ⟨B2, h2r, h2c, h2⟩ := suslin_exists_step B1 S h1c htj ht hj 1
    obtain ⟨B3, h3r, h3c, h3⟩ := suslin_exists_step B2 S h2c hjt hj ht (-1)
    obtain ⟨B4, h4r, h4c, h4⟩ := suslin_exists_step B3 S h3c htj ht hj 1
    have hB4 : (B4 : Matrix ι ι R) t j = (A : Matrix ι ι R) t t - s * q := by
      rw [h4 t j, if_pos rfl, h3 t j, if_neg hjt, h3 t t, if_pos rfl, h2 t j, if_pos rfl,
        h2 t t, if_neg htj, h1 t j, if_neg hjt, h1 t t, if_pos rfl, hAs]
      ring
    obtain ⟨M, hMr, hMc, hMtj, hMrow⟩ := IH _ hq B4 h4c hB4
    refine ⟨M, h1r.trans (h2r.trans (h3r.trans (h4r.trans hMr))), hMc, hMtj,
      fun c hct hcj ↦ ?_⟩
    rw [hMrow c hct hcj, h4 t c, if_neg hcj, h3 t c, if_neg hct, h2 t c, if_neg hcj, h1 t c,
      if_neg hct]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslin_exists_kill_entry

/-- **Killing a row.**  For `t ∉ S`, elementary moves avoiding `S` make every entry `(t, c)`
with `c ∈ T`, `c ≠ t`, `c ∉ S` zero. -/
theorem suslin_exists_row_killed (hR : HasWellFoundedDivision R) (S : Finset ι) {t : ι}
    (ht : t ∉ S) (T : Finset ι) :
    ∀ A : (Matrix ι ι R)ˣ, ClearedOn S A →
      ∃ M : (Matrix ι ι R)ˣ, Reaches A M ∧ ClearedOn S M ∧
        ∀ c ∈ T, c ≠ t → c ∉ S → (M : Matrix ι ι R) t c = 0 := by
  induction T using Finset.induction_on with
  | empty =>
      intro A hA
      exact ⟨A, Reaches.refl A, hA, fun c hc ↦ absurd hc (Finset.notMem_empty c)⟩
  | insert j T _ IH =>
      intro A hA
      obtain ⟨M, hMr, hMc, hMT⟩ := IH A hA
      by_cases hj : j = t ∨ j ∈ S
      · refine ⟨M, hMr, hMc, fun c hc hct hcS ↦ ?_⟩
        rcases Finset.mem_insert.mp hc with hcj | hcT
        · rcases hj with h | h
          · exact hct (hcj.trans h)
          · exact hcS (hcj ▸ h)
        · exact hMT c hcT hct hcS
      · obtain ⟨hjt, hjS⟩ := not_or.mp hj
        obtain ⟨M', hM'r, hM'c, hM'tj, hM'row⟩ :=
          suslin_exists_kill_entry hR S ht hjS (Ne.symm hjt) M hMc
        refine ⟨M', hMr.trans hM'r, hM'c, fun c hc hct hcS ↦ ?_⟩
        by_cases hcj : c = j
        · rw [hcj]
          exact hM'tj
        · rw [hM'row c hct hcj]
          rcases Finset.mem_insert.mp hc with hcj' | hcT
          · exact absurd hcj' hcj
          · exact hMT c hcT hct hcS

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslin_exists_row_killed

/-- **Planting a `1` on the diagonal by the Euclidean algorithm.**  The replacement of
`RankNElimination.exists_diag_one`. -/
theorem suslin_exists_diag_one (hR : HasWellFoundedDivision R) (A : (Matrix ι ι R)ˣ)
    (S : Finset ι) (hA : ClearedOn S A) (k t : ι) (hk : k ∉ S) (ht : t ∉ S) (hkt : k ≠ t) :
    ∃ M : (Matrix ι ι R)ˣ, Reaches A M ∧ ClearedOn S M ∧ (M : Matrix ι ι R) t t = 1 := by
  obtain ⟨M, hMr, hMc, hMrow⟩ := suslin_exists_row_killed hR S ht Finset.univ A hA
  have hoff : ∀ c : ι, c ≠ t → (M : Matrix ι ι R) t c = 0 := by
    intro c hct
    by_cases hcS : c ∈ S
    · rw [hMc.col hcS t, if_neg (Ne.symm hct)]
    · exact hMrow c (Finset.mem_univ c) hct hcS
  have hgw : (M : Matrix ι ι R) t t * ((M⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) t t = 1 := by
    have hv := congrFun (congrFun M.mul_inv t) t
    rw [Matrix.mul_apply, Matrix.one_apply_eq,
      Finset.sum_eq_single t
        (fun y _ hy ↦ by rw [hoff y hy, zero_mul])
        (fun hcon ↦ absurd (Finset.mem_univ t) hcon)] at hv
    exact hv
  obtain ⟨B5, h5r, h5c, h5⟩ := suslin_exists_step M S hMc (Ne.symm hkt) ht hk
    (((M⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) t t)
  obtain ⟨B6, h6r, h6c, h6⟩ := suslin_exists_step B5 S h5c hkt hk ht
    (1 - (M : Matrix ι ι R) t t)
  refine ⟨B6, hMr.trans (h5r.trans h6r), h6c, ?_⟩
  rw [h6 t t, if_pos rfl, h5 t t, if_neg (Ne.symm hkt), h5 t k, if_pos rfl, hoff k hkt,
    zero_add, hgw]
  ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslin_exists_diag_one

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
