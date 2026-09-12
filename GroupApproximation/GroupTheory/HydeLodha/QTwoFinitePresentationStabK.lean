import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationStabKSplit
import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationProduct
import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationNormal
import GroupApproximation.Meta.AxiomGuard

/-!
# Hyde–Lodha, Proposition 4.7

"For `Γ` so that `Q_n ≤ Γ ≤ Γ_n` and every nonempty finite set `K ⊂ ℤ[1/η_n]`, `Γ_K = Γ_{K+ℤ}` is of
type `F_∞`."  (Finitely presented, here.)

* `UpsilonFinitelyPresented`: Lemma 4.6, `Υ_Γ([a, b])` finitely presented for `Q₂ ≤ Γ ≤ Γ₂` and
  `a < b ≤ a + 1` in `ℤ[1/6]`, as a named hypothesis;
* `isFinitelyPresented_upsilon_inf_stabK`: `X_Γ(c, e, S) = Υ_Γ([c, e]) ∩ Γ_S` is finitely presented
  for `c < S < e ≤ c + 1`, by induction on `S` from its largest point `d`: the casing pair
  `X_Γ(c, d, s) × Υ_Γ([d, e]) ≤ X_Γ(c, e, s ∪ {d}) ≤ X_{Γ₂}(c, d, s) × Υ_{Γ₂}([d, e])`;
* `isFinitelyPresented_stabK_of_upsilon`: normalizing `K` into `[k₀, k₀ + 1)`,
  `Γ_K = X_Γ(k₀, k₀ + 1, K')`.
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson

/-- **Hyde–Lodha, Lemma 4.6**, as a named hypothesis. -/
def UpsilonFinitelyPresented : Prop :=
  ∀ Γ : Subgroup (Equiv.Perm ℚ), qTwo ≤ Γ → Γ ≤ gammaTwo → ∀ a b : ℚ, (∃ M, a ∈ Grid 6 M) →
    (∃ M, b ∈ Grid 6 M) → a < b → b ≤ a + 1 → Group.IsFinitelyPresented ↥(upsilon Γ a b)

theorem isFinitelyPresented_upsilon_inf_stabK (hU : UpsilonFinitelyPresented) (S : Finset ℚ) :
    ∀ Γ : Subgroup (Equiv.Perm ℚ), qTwo ≤ Γ → Γ ≤ gammaTwo → ∀ c e : ℚ, (∃ M, c ∈ Grid 6 M) →
      (∃ M, e ∈ Grid 6 M) → c < e → e ≤ c + 1 → (∀ k ∈ S, c < k ∧ k < e ∧ Dyadic6 k) →
        Group.IsFinitelyPresented ↥(upsilon Γ c e ⊓ stabK Γ ↑S) := by
  induction S using Finset.induction_on_max with
  | empty =>
    intro Γ hQ hΓ c e hc he hce hec _
    haveI := hU Γ hQ hΓ c e hc he hce hec
    exact Group.IsFinitelyPresented.equiv
      (MulEquiv.subgroupCongr (upsilon_inf_stabK_empty Γ c e).symm)
  | insert d s hlt ih =>
    intro Γ hQ hΓ c e hc he hce hec hS
    obtain ⟨hcd, hde, hdG⟩ := hS d (Finset.mem_insert_self d s)
    have hs : ∀ k ∈ s, c < k ∧ k < d ∧ Dyadic6 k := fun k hk =>
      ⟨(hS k (Finset.mem_insert_of_mem hk)).1, hlt k hk, (hS k (Finset.mem_insert_of_mem hk)).2.2⟩
    have hs' : ∀ k ∈ s, c < k ∧ k < d := fun k hk => ⟨(hs k hk).1, (hs k hk).2.1⟩
    have hd : ∃ M, d ∈ Grid 6 M := hdG
    have hdc : d ≤ c + 1 := by linarith
    have hed : e ≤ d + 1 := by linarith
    have hQ₂ : qTwo ≤ gammaTwo := qTwo_le_gammaTwo
    haveI := ih Γ hQ hΓ c d hc hd hcd hdc hs
    haveI := hU Γ hQ hΓ d e hd he hde hed
    haveI := ih gammaTwo hQ₂ le_rfl c d hc hd hcd hdc hs
    haveI := hU gammaTwo hQ₂ le_rfl d e hd he hde hed
    haveI : Group.IsFinitelyPresented ↥(upsilon Γ c d ⊓ stabK Γ ↑s ⊔ upsilon Γ d e) :=
      isFinitelyPresented_sup_of_commute _ _ (commute_upsilon_inf_stabK _ hec)
        (upsilon_inf_stabK_inf_upsilon_eq_bot _ hec)
    haveI hG : Group.IsFinitelyPresented
        ↥(upsilon gammaTwo c d ⊓ stabK gammaTwo ↑s ⊔ upsilon gammaTwo d e) :=
      isFinitelyPresented_sup_of_commute _ _ (commute_upsilon_inf_stabK _ hec)
        (upsilon_inf_stabK_inf_upsilon_eq_bot _ hec)
    haveI : Group.FG ↥(upsilon gammaTwo c d ⊓ stabK gammaTwo ↑s ⊔ upsilon gammaTwo d e) :=
      ProductFinitePresentation.fg_of_isFinitelyPresented _
    exact isFinitelyPresented_of_commutator_le
      (upsilon Γ c d ⊓ stabK Γ ↑s ⊔ upsilon Γ d e) (upsilon Γ c e ⊓ stabK Γ ↑(insert d s))
      (upsilon gammaTwo c d ⊓ stabK gammaTwo ↑s ⊔ upsilon gammaTwo d e)
      (sup_le (upsilon_inf_stabK_le_insert hde.le hdc) (upsilon_le_insert hcd.le hec hs'))
      ((upsilon_inf_stabK_mono hΓ c e _).trans
        (upsilon_inf_stabK_insert_gammaTwo hc hd hcd hde hec hs').le)
      (commutator_sup_le_of_commute _ _ _ (commute_upsilon_inf_stabK _ hec)
        ((commutator_upsilon_inf_stabK_le hQ c d _).trans le_sup_left)
        ((commutator_upsilon_le hQ d e).trans le_sup_right))

/-- **Hyde–Lodha, Proposition 4.7**, from Lemma 4.6. -/
theorem isFinitelyPresented_stabK_of_upsilon (hU : UpsilonFinitelyPresented)
    {Γ : Subgroup (Equiv.Perm ℚ)} (hQ : qTwo ≤ Γ) (hΓ : Γ ≤ gammaTwo) {K : Set ℚ}
    (hKfin : K.Finite) (hKne : K.Nonempty) (hKgrid : ∀ k ∈ K, Dyadic6 k) :
    Group.IsFinitelyPresented ↥(stabK Γ K) := by
  obtain ⟨k₀, hk₀⟩ := hKne
  obtain ⟨S, hSdef⟩ : ∃ S : Finset ℚ, S = (hKfin.toFinset.image (normalShift k₀)).erase k₀ :=
    ⟨_, rfl⟩
  have hScoe : (↑S : Set ℚ) = normalShift k₀ '' K \ {k₀} := by
    rw [hSdef, Finset.coe_erase, Finset.coe_image, Set.Finite.coe_toFinset]
  have hk₀G : ∃ M, k₀ ∈ Grid 6 M := hKgrid k₀ hk₀
  have hk₁G : ∃ M, k₀ + 1 ∈ Grid 6 M := by
    obtain ⟨M, hM⟩ := hk₀G
    exact ⟨M, by simpa using grid_add hM (int_mem_grid M 1)⟩
  have hS : ∀ k ∈ S, k₀ < k ∧ k < k₀ + 1 ∧ Dyadic6 k := by
    intro k hk
    rw [hSdef, Finset.mem_erase, Finset.mem_image] at hk
    obtain ⟨hne, t, ht, rfl⟩ := hk
    exact ⟨(normalShift_mem_Ioo hne).1, (normalShift_mem_Ioo hne).2,
      dyadic6_normalShift (hKgrid t (hKfin.mem_toFinset.mp ht))⟩
  haveI := isFinitelyPresented_upsilon_inf_stabK hU S Γ hQ hΓ k₀ (k₀ + 1) hk₀G hk₁G
    (by linarith) le_rfl hS
  have e : upsilon Γ k₀ (k₀ + 1) ⊓ stabK Γ ↑S = stabK Γ K := by
    rw [hScoe]
    exact (stabK_eq_upsilon_inf_stabK hΓ hk₀).symm
  exact Group.IsFinitelyPresented.equiv (MulEquiv.subgroupCongr e)

#audit_axioms GroupApproximation.HydeLodha.isFinitelyPresented_upsilon_inf_stabK
#audit_axioms GroupApproximation.HydeLodha.isFinitelyPresented_stabK_of_upsilon

end HydeLodha
end GroupApproximation
