import GroupApproximation.Algebra.BowditchCentre

/-!
# Every geodesic triangle in an H4 Cayley graph has a centre

Bowditch's Lemma 6.2.3 (*Notes on Gromov's hyperbolicity criterion*): if the Cayley
graph is `(r, L)`-H4, every geodesic triangle has a centre at constant
`M = 10 R + L`, `R = 4 r + L`.

Suppose not.  Then no vertex is within `M` of the opposite side, so the corner lemma
applies at all three vertices (`exists_cyclicCorner`).  If the corner points on one
side come in the wrong order, the one further from its vertex is a centre: it lies on
that side, within `R` of the next side through the short connecting segment, and
within `r + L` of the previous side by the fellow travelling of the initial pieces.
So the corner points come in Bowditch's cyclic order `X A D Y C E Z F B X`.  Rotating
the triangle so that its longest middle comes first,
`exists_centre_of_maxMiddle` produces a centre, a contradiction.
-/

namespace GroupApproximation
namespace DiscreteStokes

open WordMetric

universe v

variable {Q : Type v} [Group Q]

/-- **Bowditch's Lemma 6.2.3.**  In an `(r, L)`-H4 Cayley graph with `r > 0`, every
cyclic geodesic triangle has a centre at constant `10 (4 r + L) + L`. -/
theorem exists_centre_of_bowditchH4 {S : Set Q} (hS : IsSymmetricGeneratingSet S)
    {r L : ℕ} (hr : 0 < r) (hH4 : BowditchH4 S r L) {V₁ V₂ V₃ : Q} {γ₁ γ₂ γ₃ : List Q}
    (hγ₁ : IsGeodesicWord S γ₁ γ₁.prod) (hγ₂ : IsGeodesicWord S γ₂ γ₂.prod)
    (hγ₃ : IsGeodesicWord S γ₃ γ₃.prod) (h₁₂ : V₁ * γ₁.prod = V₂)
    (h₂₃ : V₂ * γ₂.prod = V₃) (h₃₁ : V₃ * γ₃.prod = V₁) :
    ∃ W, IsCentre S (10 * (4 * r + L) + L) V₁ V₂ V₃ γ₁ γ₂ γ₃ W := by
  by_contra hno
  have hrM : r ≤ 10 * (4 * r + L) + L := by omega
  have hRM : 9 * (4 * r + L) + L ≤ 10 * (4 * r + L) + L := by omega
  have hV₁γ₁ : V₁ ∈ listPoints V₁ γ₁ := start_mem_listPoints V₁ γ₁
  have hV₂γ₁ : V₂ ∈ listPoints V₁ γ₁ := by
    rw [← h₁₂]
    exact end_mem_listPoints V₁ γ₁
  have hV₂γ₂ : V₂ ∈ listPoints V₂ γ₂ := start_mem_listPoints V₂ γ₂
  have hV₃γ₂ : V₃ ∈ listPoints V₂ γ₂ := by
    rw [← h₂₃]
    exact end_mem_listPoints V₂ γ₂
  have hV₃γ₃ : V₃ ∈ listPoints V₃ γ₃ := start_mem_listPoints V₃ γ₃
  have hV₁γ₃ : V₁ ∈ listPoints V₃ γ₃ := by
    rw [← h₃₁]
    exact end_mem_listPoints V₃ γ₃
  -- no vertex is close to the opposite side
  have hfar₁ : 4 * r + L ≤ distToList S V₁ (listPoints V₂ γ₂) := by
    by_contra h
    refine hno ⟨V₁, ⟨?_, by omega, ?_⟩⟩
    · rw [distToList_eq_zero_of_mem S hV₁γ₁]
      exact Nat.zero_le _
    · rw [distToList_eq_zero_of_mem S hV₁γ₃]
      exact Nat.zero_le _
  have hfar₂ : 4 * r + L ≤ distToList S V₂ (listPoints V₃ γ₃) := by
    by_contra h
    refine hno ⟨V₂, ⟨?_, ?_, by omega⟩⟩
    · rw [distToList_eq_zero_of_mem S hV₂γ₁]
      exact Nat.zero_le _
    · rw [distToList_eq_zero_of_mem S hV₂γ₂]
      exact Nat.zero_le _
  have hfar₃ : 4 * r + L ≤ distToList S V₃ (listPoints V₁ γ₁) := by
    by_contra h
    refine hno ⟨V₃, ⟨by omega, ?_, ?_⟩⟩
    · rw [distToList_eq_zero_of_mem S hV₃γ₂]
      exact Nat.zero_le _
    · rw [distToList_eq_zero_of_mem S hV₃γ₃]
      exact Nat.zero_le _
  -- the three corners
  obtain ⟨i₁, k₁, _hi₁, _hk₁, hA₁, hA₁far, hB₁far, hA₁near, _hA₁B₁low, hA₁B₁up⟩ :=
    exists_cyclicCorner hS hr hH4 hγ₁ hγ₃ h₃₁ (by rw [h₁₂]; exact hfar₂) hfar₃
  obtain ⟨i₂, k₂, _hi₂, _hk₂, hC, hCfar, hDfar, hCnear, _hCDlow, hCDup⟩ :=
    exists_cyclicCorner hS hr hH4 hγ₂ hγ₁ h₁₂ (by rw [h₂₃]; exact hfar₃) hfar₁
  obtain ⟨i₃, k₃, _hi₃, _hk₃, hF, hFfar, hEfar, hFnear, _hFElow, hFEup⟩ :=
    exists_cyclicCorner hS hr hH4 hγ₃ hγ₂ h₂₃ (by rw [h₃₁]; exact hfar₁) hfar₂
  -- the corner points come in Bowditch's cyclic order
  have ho₁ : i₁ ≤ γ₁.length - k₂ := by
    by_contra h
    refine hno ⟨V₁ * (γ₁.take (γ₁.length - k₂)).prod, ⟨?_, ?_, ?_⟩⟩
    · rw [distToList_eq_zero_of_mem S (take_mem_listPoints V₁ γ₁ _)]
      exact Nat.zero_le _
    · have h1 := distToList_le_of_mem S (V₁ * (γ₁.take (γ₁.length - k₂)).prod)
        (take_mem_listPoints V₂ γ₂ i₂)
      have h2 := wordDist_comm hS (V₁ * (γ₁.take (γ₁.length - k₂)).prod)
        (V₂ * (γ₂.take i₂).prod)
      omega
    · have h1 := hA₁near (γ₁.length - k₂) (by omega)
      omega
  have ho₂ : i₂ ≤ γ₂.length - k₃ := by
    by_contra h
    refine hno ⟨V₂ * (γ₂.take (γ₂.length - k₃)).prod, ⟨?_, ?_, ?_⟩⟩
    · have h1 := hCnear (γ₂.length - k₃) (by omega)
      omega
    · rw [distToList_eq_zero_of_mem S (take_mem_listPoints V₂ γ₂ _)]
      exact Nat.zero_le _
    · have h1 := distToList_le_of_mem S (V₂ * (γ₂.take (γ₂.length - k₃)).prod)
        (take_mem_listPoints V₃ γ₃ i₃)
      have h2 := wordDist_comm hS (V₂ * (γ₂.take (γ₂.length - k₃)).prod)
        (V₃ * (γ₃.take i₃).prod)
      omega
  have ho₃ : i₃ ≤ γ₃.length - k₁ := by
    by_contra h
    refine hno ⟨V₃ * (γ₃.take (γ₃.length - k₁)).prod, ⟨?_, ?_, ?_⟩⟩
    · have h1 := distToList_le_of_mem S (V₃ * (γ₃.take (γ₃.length - k₁)).prod)
        (take_mem_listPoints V₁ γ₁ i₁)
      have h2 := wordDist_comm hS (V₃ * (γ₃.take (γ₃.length - k₁)).prod)
        (V₁ * (γ₁.take i₁).prod)
      omega
    · have h1 := hFnear (γ₃.length - k₁) (by omega)
      omega
    · rw [distToList_eq_zero_of_mem S (take_mem_listPoints V₃ γ₃ _)]
      exact Nat.zero_le _
  -- the longest middle gives a centre
  have hcase₁ : γ₂.length - k₃ - i₂ ≤ γ₁.length - k₂ - i₁ →
      γ₃.length - k₁ - i₃ ≤ γ₁.length - k₂ - i₁ → False := by
    intro h1 h2
    obtain ⟨W, hW⟩ := exists_centre_of_maxMiddle hS hH4 hrM hRM hγ₁ hγ₂ hγ₃ ho₁
      (by omega) ho₂ ho₃ hA₁B₁up hB₁far hC hCfar hCDup hFEup h1 h2
    exact hno ⟨W, hW⟩
  have hcase₂ : γ₃.length - k₁ - i₃ ≤ γ₂.length - k₃ - i₂ →
      γ₁.length - k₂ - i₁ ≤ γ₂.length - k₃ - i₂ → False := by
    intro h1 h2
    obtain ⟨W, hW⟩ := exists_centre_of_maxMiddle hS hH4 hrM hRM hγ₂ hγ₃ hγ₁ ho₂
      (by omega) ho₃ ho₁ hCDup hDfar hF hFfar hFEup hA₁B₁up h1 h2
    exact hno ⟨W, hW.rotate.rotate⟩
  have hcase₃ : γ₁.length - k₂ - i₁ ≤ γ₃.length - k₁ - i₃ →
      γ₂.length - k₃ - i₂ ≤ γ₃.length - k₁ - i₃ → False := by
    intro h1 h2
    obtain ⟨W, hW⟩ := exists_centre_of_maxMiddle hS hH4 hrM hRM hγ₃ hγ₁ hγ₂ ho₃
      (by omega) ho₁ ho₂ hFEup hEfar hA₁ hA₁far hA₁B₁up hCDup h1 h2
    exact hno ⟨W, hW.rotate⟩
  rcases le_total (γ₂.length - k₃ - i₂) (γ₁.length - k₂ - i₁) with h21 | h12
  · rcases le_total (γ₃.length - k₁ - i₃) (γ₁.length - k₂ - i₁) with h31 | h13
    · exact hcase₁ h21 h31
    · exact hcase₃ h13 (le_trans h21 h13)
  · rcases le_total (γ₃.length - k₁ - i₃) (γ₂.length - k₃ - i₂) with h32 | h23
    · exact hcase₂ h32 h12
    · exact hcase₃ (le_trans h12 h23) h23

end DiscreteStokes
end GroupApproximation

#audit_axioms GroupApproximation.DiscreteStokes.exists_centre_of_bowditchH4
