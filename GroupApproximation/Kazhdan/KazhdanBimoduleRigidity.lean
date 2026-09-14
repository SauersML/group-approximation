import GroupApproximation.Kazhdan.KazhdanNearInvariantVector
import GroupApproximation.Kazhdan.KazhdanComplex
import GroupApproximation.Meta.AxiomGuard

/-!
# Rigidity of bimodule representations of a Kazhdan group

The step of `simple_kazhdan_sofic_group.tex` (origin/main 696c4b602, section "Word problems and factors",
tex l.544–546)

> The proof of~\cite[Theorem~2]{OzawaUniversal} then shows that the unitary group of a separable
> $\mathrm{II}_1$ factor contains $G_X$ for only countably many $X$.

rests on one rigidity estimate for a Kazhdan group `Γ`, proved here on an abstract complex Hilbert space,
with no von Neumann algebra.  `L₁` and `L₂` are left actions and `R₂` is a right action by isometries,
modelled on `L²(M)` with `L_i(g) ξ = u_i(g) ξ` and `R₂(g) ξ = ξ u₂(g)*`.  The hypotheses are:

* `L₁` commutes with `R₂`;
* `R₂(g) Ω = L₂(g⁻¹) Ω`, the right and left actions agree on the trace vector;
* `R₂` and `L₂` have the same kernel;
* `Γ / ker L₁` and `Γ / ker L₂` are simple (`IsMaximalNormal`), and the kernels differ.

`bimodule_rigidity`: if `‖L₁(s)Ω − L₂(s)Ω‖ < εδ` for `s` in the Kazhdan set, then `‖L₁(g)Ω − Ω‖ < 2δ` for
every `g ∈ Γ`.  The route is Ozawa's:

1. `ρ(g) = L₁(g) R₂(g)` is a representation moving `Ω` by `‖L₁(s)Ω − L₂(s)Ω‖`, so property (T) gives an
   invariant vector `ζ` within `δ` of `Ω` (`KazhdanNearInvariantVector.exists_invariant_near`, over the
   realification `realifyHom`).
2. `{g : L₁(g)ζ = ζ}` and `{g : R₂(g)ζ = ζ}` are normal subgroups containing `ker L₁` and `ker L₂`.  An
   element in one kernel and not the other lies in one of them, which is then all of `Γ` by simplicity.
3. Hence `L₁(Γ)` fixes `ζ`, and `‖L₁(g)Ω − Ω‖ ≤ 2‖Ω − ζ‖ < 2δ`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace KazhdanBimoduleRigidity

universe u v

variable {Γ : Type u} [Group Γ]

/-- `N` is maximal among normal subgroups: `Γ / N` is simple or trivial. -/
def IsMaximalNormal (N : Subgroup Γ) : Prop :=
  ∀ K : Subgroup Γ, K.Normal → N ≤ K → K = N ∨ K = ⊤

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The product representation `g ↦ L₁(g) R₂(g)` of commuting actions. -/
noncomputable def productRep (L₁ R₂ : Γ →* (H ≃ₗᵢ[ℂ] H))
    (hcomm : ∀ g h, L₁ g * R₂ h = R₂ h * L₁ g) : Γ →* (H ≃ₗᵢ[ℂ] H) where
  toFun g := L₁ g * R₂ g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, mul_assoc]
    rw [← mul_assoc (L₁ h) (R₂ g), hcomm h g, mul_assoc (R₂ g)]

theorem apply_inv_apply (e : Γ →* (H ≃ₗᵢ[ℂ] H)) (g : Γ) (x : H) : e g⁻¹ (e g x) = x := by
  change (e g⁻¹ * e g) x = x
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

theorem apply_apply_inv (e : Γ →* (H ≃ₗᵢ[ℂ] H)) (g : Γ) (x : H) : e g (e g⁻¹ x) = x := by
  change (e g * e g⁻¹) x = x
  rw [← map_mul, mul_inv_cancel, map_one]
  rfl

/-- The elements fixing a vector, as a subgroup of `Γ`. -/
def fixer (e : Γ →* (H ≃ₗᵢ[ℂ] H)) (ζ : H) : Subgroup Γ where
  carrier := {g | e g ζ = ζ}
  one_mem' := by
    show e 1 ζ = ζ
    rw [map_one]
    rfl
  mul_mem' := by
    intro a b ha hb
    have ha' : e a ζ = ζ := ha
    have hb' : e b ζ = ζ := hb
    show e (a * b) ζ = ζ
    rw [map_mul]
    change e a (e b ζ) = ζ
    rw [hb', ha']
  inv_mem' := by
    intro a ha
    have ha' : e a ζ = ζ := ha
    show e a⁻¹ ζ = ζ
    calc e a⁻¹ ζ = e a⁻¹ (e a ζ) := by rw [ha']
      _ = ζ := apply_inv_apply e a ζ

theorem ker_le_fixer (e : Γ →* (H ≃ₗᵢ[ℂ] H)) (ζ : H) : e.ker ≤ fixer e ζ := by
  intro g hg
  show e g ζ = ζ
  rw [MonoidHom.mem_ker.mp hg]
  rfl

/-- **Ozawa's rigidity estimate** for a Kazhdan group (tex l.544–546).  If `L₁` and `L₂` move the
trace vector `Ω` by nearly the same amount on the Kazhdan set, their kernels differ, and both quotients
are simple, then `L₁` moves `Ω` by less than `2δ` everywhere. -/
theorem bimodule_rigidity {Q : Finset Γ} {ε : ℝ} (hQ : IsKazhdanPair.{u, v} Γ Q ε) (Ω : H)
    (L₁ L₂ R₂ : Γ →* (H ≃ₗᵢ[ℂ] H)) (hcomm : ∀ g h, L₁ g * R₂ h = R₂ h * L₁ g)
    (hRΩ : ∀ g, R₂ g Ω = L₂ g⁻¹ Ω) (hker : R₂.ker = L₂.ker)
    (hmax₁ : IsMaximalNormal L₁.ker) (hmax₂ : IsMaximalNormal L₂.ker) (hne : L₁.ker ≠ L₂.ker)
    {δ : ℝ} (hδ : 0 < δ) (hclose : ∀ s ∈ Q, ‖L₁ s Ω - L₂ s Ω‖ < ε * δ) :
    ∀ g, ‖L₁ g Ω - Ω‖ < 2 * δ := by
  letI : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  let ρ := productRep L₁ R₂ hcomm
  have hmove : ∀ s ∈ Q, ‖realifyHom ρ s Ω - Ω‖ < ε * δ := by
    intro s hs
    have h1 : realifyHom ρ s Ω = R₂ s (L₁ s Ω) := by
      change (L₁ s * R₂ s) Ω = R₂ s (L₁ s Ω)
      rw [hcomm s s]
      rfl
    have h2 : R₂ s (L₂ s Ω) = Ω := by
      have h := hRΩ s⁻¹
      rw [inv_inv] at h
      rw [← h]
      exact apply_apply_inv R₂ s Ω
    calc ‖realifyHom ρ s Ω - Ω‖ = ‖R₂ s (L₁ s Ω) - R₂ s (L₂ s Ω)‖ := by rw [h1, h2]
      _ = ‖L₁ s Ω - L₂ s Ω‖ := by rw [← map_sub, LinearIsometryEquiv.norm_map]
      _ < ε * δ := hclose s hs
  obtain ⟨ζ, hζ, hnear⟩ :=
    KazhdanNearInvariantVector.exists_invariant_near hQ (realifyHom ρ) Ω hδ hmove
  have hinv : ∀ g, L₁ g (R₂ g ζ) = ζ := fun g ↦ hζ g
  have hRL : ∀ h, R₂ h ζ = L₁ h⁻¹ ζ := by
    intro h
    calc R₂ h ζ = L₁ h⁻¹ (L₁ h (R₂ h ζ)) := (apply_inv_apply L₁ h _).symm
      _ = L₁ h⁻¹ ζ := by rw [hinv h]
  have hnormL : (fixer L₁ ζ).Normal := by
    refine ⟨fun g hg h ↦ ?_⟩
    have hg' : L₁ g ζ = ζ := hg
    show L₁ (h * g * h⁻¹) ζ = ζ
    rw [map_mul, map_mul]
    change L₁ h (L₁ g (L₁ h⁻¹ ζ)) = ζ
    rw [← hRL h]
    change L₁ h ((L₁ g * R₂ h) ζ) = ζ
    rw [hcomm g h]
    change L₁ h (R₂ h (L₁ g ζ)) = ζ
    rw [hg', hinv h]
  have hnormR : (fixer R₂ ζ).Normal := by
    refine ⟨fun g hg h ↦ ?_⟩
    have hg' : R₂ g ζ = ζ := hg
    have hRL' : R₂ h⁻¹ ζ = L₁ h ζ := by rw [hRL h⁻¹, inv_inv]
    show R₂ (h * g * h⁻¹) ζ = ζ
    rw [map_mul, map_mul]
    change R₂ h (R₂ g (R₂ h⁻¹ ζ)) = ζ
    rw [hRL']
    change R₂ h ((R₂ g * L₁ h) ζ) = ζ
    rw [← hcomm h g]
    change R₂ h (L₁ h (R₂ g ζ)) = ζ
    rw [hg']
    change (R₂ h * L₁ h) ζ = ζ
    rw [← hcomm h h]
    exact hinv h
  have htop : fixer L₁ ζ = ⊤ := by
    by_cases h21 : L₂.ker ≤ L₁.ker
    · have h12 : ¬ L₁.ker ≤ L₂.ker := fun h12 ↦ hne (le_antisymm h12 h21)
      obtain ⟨n, hn₁, hn₂⟩ := SetLike.not_le_iff_exists.mp h12
      have hn₁' : L₁ n = 1 := MonoidHom.mem_ker.mp hn₁
      have hnR : n ∈ fixer R₂ ζ := by
        show R₂ n ζ = ζ
        have h := hinv n
        rw [hn₁'] at h
        exact h
      have hle : L₂.ker ≤ fixer R₂ ζ := by
        rw [← hker]
        exact ker_le_fixer R₂ ζ
      have hRtop : fixer R₂ ζ = ⊤ := by
        rcases hmax₂ (fixer R₂ ζ) hnormR hle with h | h
        · rw [h] at hnR
          exact absurd hnR hn₂
        · exact h
      refine top_unique fun g _ ↦ ?_
      show L₁ g ζ = ζ
      have hg : g ∈ fixer R₂ ζ := by
        rw [hRtop]
        exact Subgroup.mem_top g
      have hg' : R₂ g ζ = ζ := hg
      calc L₁ g ζ = L₁ g (R₂ g ζ) := by rw [hg']
        _ = ζ := hinv g
    · obtain ⟨n, hn₂, hn₁⟩ := SetLike.not_le_iff_exists.mp h21
      have hn₂R : n ∈ R₂.ker := by
        rw [hker]
        exact hn₂
      have hn₂' : R₂ n = 1 := MonoidHom.mem_ker.mp hn₂R
      have hnL : n ∈ fixer L₁ ζ := by
        show L₁ n ζ = ζ
        have h := hinv n
        rw [hn₂'] at h
        exact h
      rcases hmax₁ (fixer L₁ ζ) hnormL (ker_le_fixer L₁ ζ) with h | h
      · rw [h] at hnL
        exact absurd hnL hn₁
      · exact h
  have hfix : ∀ g, L₁ g ζ = ζ := by
    intro g
    have hg : g ∈ fixer L₁ ζ := by
      rw [htop]
      exact Subgroup.mem_top g
    exact hg
  intro g
  have hsplit : L₁ g Ω - Ω = L₁ g (Ω - ζ) + (ζ - Ω) := by
    rw [map_sub, hfix g]
    abel
  calc ‖L₁ g Ω - Ω‖ = ‖L₁ g (Ω - ζ) + (ζ - Ω)‖ := by rw [hsplit]
    _ ≤ ‖L₁ g (Ω - ζ)‖ + ‖ζ - Ω‖ := norm_add_le _ _
    _ = ‖Ω - ζ‖ + ‖Ω - ζ‖ := by rw [LinearIsometryEquiv.norm_map, norm_sub_rev ζ Ω]
    _ < 2 * δ := by linarith

#audit_axioms bimodule_rigidity

end KazhdanBimoduleRigidity
end GroupApproximation
