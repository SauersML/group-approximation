import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.WordMultiplier.Siblings
import GroupApproximation.Meta.AxiomGuard

/-!
# The sibling kernel and complement coordinates

Lane `sk-leavitt-08`, Khanh (arXiv:2609.08428v1), proof of Lemma 4.1 (`lem:word-multiplier`).

Khanh, tex l.352: "Consequently
$$\ker\eta^*=\bigoplus_{\ell=1}^h s_\ell R, \eqnum[eq:sibling-kernel]$$
with inverse coordinate maps $(r_\ell)_\ell\mapsto\sum_\ell s_\ell r_\ell$ and
$z\mapsto(s_\ell^*z)_\ell$. If $y=a_ix$ and $b=\eta_i^*$, then $by=1$, and
$R\oplus\ker b\rightleftarrows R$, $(t,z)\longmapsto yt+z$ and $u\longmapsto(bu,u-ybu)$
are mutually inverse. The kernel in~\eqref{eq:sibling-kernel} is nonzero because $h\geq1$ and
$s_\ell^*s_\ell=1$."

## Route

In any ring with a Leavitt family, `η^* = wordT η`, `s_ℓ = wordS (sibling η ℓ)`.
* `eq_sum_sibling_of_wordT_mul_eq_zero`: multiply `z` by the complete leaf-set identity.
* `wordT_mul_sum_sibling`, `wordT_sibling_mul_sum`: the forward map lands in the kernel and
  the coordinate maps invert it (prefix orthogonality).
* `complement_coordinates`, `complement_forward`: the two maps `R ⊕ ker b ⇄ R`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open scoped BigOperators

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- The complete-leaf-set identity indexed by `Fin |η|`. -/
theorem cylinder_add_sum_sibling (η : List (Fin 2)) :
    L.cylinder η + ∑ ℓ : Fin η.length, L.cylinder (sibling η ℓ) = 1 := by
  have h := cylinder_take_add_sum_sibling L η η.length le_rfl
  rw [List.take_length, ← Fin.sum_univ_eq_sum_range] at h
  exact h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cylinder_add_sum_sibling

/-- `η^* s_ℓ = 0`. -/
theorem wordT_eta_mul_wordS_sibling (η : List (Fin 2)) (ℓ : Fin η.length) :
    L.wordT η * L.wordS (sibling η ℓ) = 0 :=
  LeavittFamily.wordT_mul_wordS_of_incomparable L _ _
    (eta_not_prefix_sibling η ℓ.isLt) (sibling_not_prefix_eta η ℓ.isLt)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.wordT_eta_mul_wordS_sibling

/-- `s_j^* s_ℓ = δ_{jℓ}`. -/
theorem wordT_sibling_mul_wordS_sibling (η : List (Fin 2)) (j ℓ : Fin η.length) :
    L.wordT (sibling η j) * L.wordS (sibling η ℓ) = if j = ℓ then 1 else 0 := by
  by_cases hjl : j = ℓ
  · subst hjl
    rw [if_pos rfl, LeavittFamily.wordT_mul_wordS_self]
  · rw [if_neg hjl]
    exact LeavittFamily.wordT_mul_wordS_of_incomparable L _ _
      (sibling_incomparable η (fun h => hjl (Fin.ext h)) j.isLt ℓ.isLt)
      (sibling_incomparable η (fun h => hjl (Fin.ext h).symm) ℓ.isLt j.isLt)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.wordT_sibling_mul_wordS_sibling

/-- Every element of `ker η^*` is `∑_ℓ s_ℓ (s_ℓ^* z)` (eq:sibling-kernel, inverse map). -/
theorem eq_sum_sibling_of_wordT_mul_eq_zero (η : List (Fin 2)) (z : A)
    (hz : L.wordT η * z = 0) :
    z = ∑ ℓ : Fin η.length, L.wordS (sibling η ℓ) * (L.wordT (sibling η ℓ) * z) := by
  calc
    z = (L.cylinder η + ∑ ℓ : Fin η.length, L.cylinder (sibling η ℓ)) * z := by
      rw [cylinder_add_sum_sibling L η, one_mul]
    _ = L.wordS η * (L.wordT η * z) +
        ∑ ℓ : Fin η.length, L.wordS (sibling η ℓ) * (L.wordT (sibling η ℓ) * z) := by
      rw [add_mul, Finset.sum_mul]
      simp only [LeavittFamily.cylinder, mul_assoc]
    _ = ∑ ℓ : Fin η.length, L.wordS (sibling η ℓ) * (L.wordT (sibling η ℓ) * z) := by
      rw [hz, mul_zero, zero_add]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.eq_sum_sibling_of_wordT_mul_eq_zero

/-- The forward coordinate map lands in `ker η^*`. -/
theorem wordT_mul_sum_sibling (η : List (Fin 2)) (r : Fin η.length → A) :
    L.wordT η * ∑ ℓ : Fin η.length, L.wordS (sibling η ℓ) * r ℓ = 0 := by
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun ℓ _ => ?_
  rw [← mul_assoc, wordT_eta_mul_wordS_sibling L η ℓ, zero_mul]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.wordT_mul_sum_sibling

/-- The coordinate maps `z ↦ (s_j^* z)_j` recover the coefficients. -/
theorem wordT_sibling_mul_sum (η : List (Fin 2)) (r : Fin η.length → A) (j : Fin η.length) :
    L.wordT (sibling η j) * ∑ ℓ : Fin η.length, L.wordS (sibling η ℓ) * r ℓ = r j := by
  rw [Finset.mul_sum, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · rw [← mul_assoc, LeavittFamily.wordT_mul_wordS_self, one_mul]
  · intro ℓ _ hne
    rw [← mul_assoc, wordT_sibling_mul_wordS_sibling L η j ℓ, if_neg (fun h => hne h.symm),
      zero_mul]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.wordT_sibling_mul_sum

/-- **eq:sibling-kernel**: `ker η^* = ⊕_ℓ s_ℓ R`, as an explicit parametrisation. -/
theorem wordT_mul_eq_zero_iff (η : List (Fin 2)) (z : A) :
    L.wordT η * z = 0 ↔
      ∃ r : Fin η.length → A, z = ∑ ℓ : Fin η.length, L.wordS (sibling η ℓ) * r ℓ := by
  constructor
  · intro hz
    exact ⟨fun ℓ => L.wordT (sibling η ℓ) * z, eq_sum_sibling_of_wordT_mul_eq_zero L η z hz⟩
  · rintro ⟨r, rfl⟩
    exact wordT_mul_sum_sibling L η r

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.wordT_mul_eq_zero_iff

/-- The sibling kernel is nonzero when `η` is nonempty: `s_1` lies in it and `s_1^* s_1 = 1`. -/
theorem exists_ne_zero_wordT_mul_eq_zero [Nontrivial A] (η : List (Fin 2)) (hη : η ≠ []) :
    ∃ z : A, z ≠ 0 ∧ L.wordT η * z = 0 := by
  have h0 : 0 < η.length := List.length_pos_iff.mpr hη
  refine ⟨L.wordS (sibling η 0), fun hz => one_ne_zero ?_, ?_⟩
  · have h1 := wordT_sibling_mul_wordS_sibling L η ⟨0, h0⟩ ⟨0, h0⟩
    rw [if_pos rfl] at h1
    rw [← h1]
    exact (congrArg (fun w => L.wordT (sibling η 0) * w) hz).trans (mul_zero _)
  · exact wordT_eta_mul_wordS_sibling L η ⟨0, h0⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.exists_ne_zero_wordT_mul_eq_zero

/-- `u ↦ (bu, u - ybu)` lands in `R ⊕ ker b` and `(t,z) ↦ yt+z` undoes it. -/
theorem complement_coordinates {b y : A} (hby : b * y = 1) (u : A) :
    b * (u - y * (b * u)) = 0 ∧ y * (b * u) + (u - y * (b * u)) = u := by
  refine ⟨?_, by abel⟩
  rw [mul_sub, ← mul_assoc b y, hby, one_mul, sub_self]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.complement_coordinates

/-- `(t,z) ↦ yt+z` followed by `u ↦ (bu, u - ybu)` is the identity on `R ⊕ ker b`. -/
theorem complement_forward {b y : A} (hby : b * y = 1) (t z : A) (hz : b * z = 0) :
    b * (y * t + z) = t ∧ y * t + z - y * (b * (y * t + z)) = z := by
  have h : b * (y * t + z) = t := by
    rw [mul_add, ← mul_assoc b y, hby, one_mul, hz, add_zero]
  refine ⟨h, ?_⟩
  rw [h]
  abel

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.complement_forward

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
