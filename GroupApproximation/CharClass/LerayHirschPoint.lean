import GroupApproximation.CharClass.LerayHirschHomotopy
import GroupApproximation.CharClass.ProjectiveSpaceRing
import GroupApproximation.CharClass.CohomologyDegreeZero
import GroupApproximation.CharClass.CohomologyAssoc

/-!
# Leray–Hirsch over a point

The base case of the cover induction.  Over a space with the cohomology of a
point, the column has exactly one summand that is not forced to vanish: in degree
`n` the `i`-th entry lies in `H^{n-2i}` of the base, which is zero unless
`n = 2i`.  So the Leray–Hirsch map in degree `2m` is `z ↦ π^*(z) ⌣ ξ^m`, between
two lines, and it is bijective exactly when `ξ^m ≠ 0`.

That is the whole content, and it is why the base case needs only the ADDITIVE
cohomology of the fibre together with the non-vanishing of the powers.  For a
fibre `ℂP^1` the powers are `1` and `ξ`, both nonzero for elementary reasons, so
this case is available before any ring structure is known.

## Main declarations

* `bijective_of_trivial` — a map between trivial groups.
* `bijective_lhSum_point` — **the base case**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable {Z Y : TopCat.{0}}

theorem bijective_of_trivial {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (φ : M →+ N) (hM : ∀ x : M, x = 0) (hN : ∀ y : N, y = 0) :
    Function.Bijective φ :=
  ⟨fun x y _ => (hM x).trans (hM y).symm,
    fun y => ⟨0, by rw [map_zero]; exact (hN y).symm⟩⟩

/-- **Leray–Hirsch over a point.**  The base has the cohomology of a point, the
total space that of `ℂP^d`, and the powers of `ξ` up to `d` are nonzero. -/
theorem bijective_lhSum_point (π : Y ⟶ Z)
    (hZ0 : Hmod2 Z 0 ≃ₗ[ZMod 2] ZMod 2)
    (hone : one Z ≠ (0 : Hmod2 Z 0))
    (hZv : ∀ k : ℕ, k ≠ 0 → ∀ a : Hmod2 Z k, a = 0)
    (ξ : Hmod2 Y 2) (d : ℕ)
    (hYline : ∀ m : ℕ, m ≤ d → Nonempty (Hmod2 Y (2 * m) ≃ₗ[ZMod 2] ZMod 2))
    (hYv : ∀ k : ℕ, (∀ m : ℕ, m ≤ d → k ≠ 2 * m) → ∀ a : Hmod2 Y k, a = 0)
    (hpow : ∀ m : ℕ, m ≤ d → cupPowE ξ m ≠ 0)
    (n : ℕ) : Function.Bijective (lhSum π ξ (d + 1) n) := by
  by_cases hn : ∃ m : ℕ, m ≤ d ∧ n = 2 * m
  · obtain ⟨m, hmd, rfl⟩ := hn
    have hmlt : m < d + 1 := by omega
    have he : 2 * m - 2 * m = 0 := by omega
    -- Every summand but the `m`-th is forced to vanish.
    have hzero : ∀ (c : lhDomain Z (d + 1) (2 * m)) (i : Fin (d + 1)), (i : ℕ) ≠ m →
        (c : (j : Fin (d + 1)) → Hmod2 Z (2 * m - 2 * (j : ℕ))) i = 0 := by
      intro c i hi
      by_cases hlt : 2 * m < 2 * (i : ℕ)
      · exact lhDomain_vanish c i hlt
      · exact hZv _ (by omega) _
    have hsum : ∀ c : lhDomain Z (d + 1) (2 * m),
        lhSum π ξ (d + 1) (2 * m) c
          = lhTerm π ξ (2 * m) m
            ((c : (j : Fin (d + 1)) → Hmod2 Z (2 * m - 2 * (j : ℕ)))
              (⟨m, hmlt⟩ : Fin (d + 1))) := by
      intro c
      rw [lhSum_apply]
      refine Finset.sum_eq_single (⟨m, hmlt⟩ : Fin (d + 1)) ?_ ?_
      · intro b _ hb
        rw [hzero c b (fun hbm => hb (Fin.ext hbm)), lhTerm_zero]
      · intro hmem
        exact absurd (Finset.mem_univ (⟨m, hmlt⟩ : Fin (d + 1))) hmem
    -- On the generator of the domain the map hits `ξ^m`.
    have hval : lhTerm π ξ (2 * m) m (cohCast he.symm (one Z)) = cupPowE ξ m := by
      rw [lhTerm_of_le π ξ (le_refl (2 * m)), pull_cohCast, pull_one, cup_cohCast_left,
        one_cup', cohCast_cohCast, cohCast_cohCast]
      exact cohCast_self _ _
    have hgen : lhTerm π ξ (2 * m) m (cohCast he.symm (one Z)) ≠ 0 := by
      rw [hval]
      exact hpow m hmd
    constructor
    · -- injectivity, through the kernel
      have hker : ∀ c : lhDomain Z (d + 1) (2 * m),
          lhSum π ξ (d + 1) (2 * m) c = 0 → c = 0 := by
        intro c hc
        rw [hsum] at hc
        have hz : (c : (j : Fin (d + 1)) → Hmod2 Z (2 * m - 2 * (j : ℕ)))
            (⟨m, hmlt⟩ : Fin (d + 1)) = 0 := by
          by_contra hne
          have h1 : cohCast he ((c : (j : Fin (d + 1)) → Hmod2 Z (2 * m - 2 * (j : ℕ)))
              (⟨m, hmlt⟩ : Fin (d + 1))) ≠ 0 :=
            fun hcc => hne ((cohCast_eq_zero_iff he _).mp hcc)
          have h2 : cohCast he ((c : (j : Fin (d + 1)) → Hmod2 Z (2 * m - 2 * (j : ℕ)))
              (⟨m, hmlt⟩ : Fin (d + 1))) = one Z := by
            rw [eq_lineGen_of_ne_zero hZ0 h1]
            exact (eq_lineGen_of_ne_zero hZ0 hone).symm
          have h3 : (c : (j : Fin (d + 1)) → Hmod2 Z (2 * m - 2 * (j : ℕ)))
              (⟨m, hmlt⟩ : Fin (d + 1)) = cohCast he.symm (one Z) := by
            rw [← h2, cohCast_cohCast, cohCast_self]
          rw [h3] at hc
          exact hgen hc
        refine lhDomain_ext fun i => ?_
        rw [lhDomain_zero_apply]
        by_cases hi : (i : ℕ) = m
        · rw [show i = (⟨m, hmlt⟩ : Fin (d + 1)) from Fin.ext hi]
          exact hz
        · exact hzero c i hi
      intro c c' h
      have := hker (c - c') (by rw [map_sub, h, sub_self])
      exact sub_eq_zero.mp this
    · -- surjectivity, because both sides are lines
      intro y
      obtain ⟨eY⟩ := hYline m hmd
      rcases eq_zero_or_eq_of_line eY hgen y with hy | hy
      · exact ⟨0, by rw [map_zero, hy]⟩
      · refine ⟨⟨fun j => if h : (j : ℕ) = m
            then cohCast (show (0 : ℕ) = 2 * m - 2 * (j : ℕ) by omega) (one Z)
            else 0, ?_⟩, ?_⟩
        · intro j hj
          exact dif_neg (by omega)
        · rw [hsum, hy]
          show lhTerm π ξ (2 * m) m
            (if h : ((⟨m, hmlt⟩ : Fin (d + 1)) : ℕ) = m
              then cohCast (show (0 : ℕ) = 2 * m - 2 * ((⟨m, hmlt⟩ : Fin (d + 1)) : ℕ)
                by omega) (one Z)
              else 0) = _
          rw [dif_pos rfl, hval]
  · -- both sides vanish
    refine bijective_of_trivial _ ?_ ?_
    · intro c
      refine lhDomain_ext fun i => ?_
      rw [lhDomain_zero_apply]
      by_cases hi : n < 2 * (i : ℕ)
      · exact lhDomain_vanish c i hi
      · refine hZv _ ?_ _
        intro hzz
        have hid : (i : ℕ) < d + 1 := i.2
        exact hn ⟨(i : ℕ), by omega, by omega⟩
    · intro a
      refine hYv n ?_ a
      intro mm hmm hnm
      exact hn ⟨mm, hmm, hnm⟩

end

end LH
end CharClass
end GroupApproximation
