import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.CloseCPAP
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-25, part 2: the weighted multiplicativity estimate

Let `D = ρ(ab) − ρ(a)ρ(b)`.  Since `ρ` preserves stars,

`D⋆D = ρ((ab)⋆)ρ(ab) − ρ((ab)⋆)(ρ(a)ρ(b)) − ρ(b⋆)(ρ(a⋆)ρ(ab)) + ρ(b⋆)(ρ(a⋆)(ρ(a)ρ(b)))`.

Four chains of `norm_bimod_step`, starting from `ψρ(ab) ≈ ab` and `ψ(ρ(a)ρ(b)) ≈ ab`,
move each term close to `(ab)⋆(ab)` or to `b⋆(a⋆(ab))`.  These values cancel in pairs,
so `ψ(D⋆D)` is bounded by an explicit polynomial in `δ` and `K`.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

/-- **The weighted multiplicativity estimate.**  From left bimodularity at `a`, `a⋆`, `b⋆`
and `(ab)⋆`, together with `ψρ(b) ≈ b` and `ψρ(ab) ≈ ab`, the norm of `ψ(D⋆D)` with
`D = ρ(ab) − ρ(a)ρ(b)` is bounded by an explicit polynomial of degree three in `K`. -/
theorem norm_psi_star_mul_defect_le {A : Type u} [CStarAlgebra A] {Y : FiniteModel}
    (ρ : A →ₗ[ℂ] Matrix Y Y ℂ) (ψ : Matrix Y Y ℂ →ₗ[ℂ] A)
    (hρs : ∀ a : A, ρ (star a) = star (ρ a)) {a b : A} {δ K : ℝ} (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (ha : ∀ M : Matrix Y Y ℂ, ‖ψ (ρ a * M) - a * ψ M‖ ≤ δ * ‖M‖)
    (hsa : ∀ M : Matrix Y Y ℂ, ‖ψ (ρ (star a) * M) - star a * ψ M‖ ≤ δ * ‖M‖)
    (hsb : ∀ M : Matrix Y Y ℂ, ‖ψ (ρ (star b) * M) - star b * ψ M‖ ≤ δ * ‖M‖)
    (hsab : ∀ M : Matrix Y Y ℂ,
      ‖ψ (ρ (star (a * b)) * M) - star (a * b) * ψ M‖ ≤ δ * ‖M‖)
    (haK : ‖a‖ ≤ K) (hsaK : ‖star a‖ ≤ K) (hsbK : ‖star b‖ ≤ K)
    (hsabK : ‖star (a * b)‖ ≤ K) (hRa : ‖ρ a‖ ≤ K) (hRb : ‖ρ b‖ ≤ K)
    (hRab : ‖ρ (a * b)‖ ≤ K) (hRsa : ‖ρ (star a)‖ ≤ K)
    (hb : ‖ψ (ρ b) - b‖ ≤ δ) (hab : ‖ψ (ρ (a * b)) - a * b‖ ≤ δ) :
    ‖ψ (star (ρ (a * b) - ρ a * ρ b) * (ρ (a * b) - ρ a * ρ b))‖
      ≤ (δ * K + K * δ) + (δ * (K * K) + K * (δ * K + K * δ))
        + (δ * (K * K) + K * (δ * K + K * δ))
        + (δ * (K * (K * K)) + K * (δ * (K * K) + K * (δ * K + K * δ))) := by
  have e1 : ‖ψ (ρ a * ρ b) - a * b‖ ≤ δ * K + K * δ :=
    norm_bimod_step ρ ψ ha hδ haK hRb hb
  have hRaRb : ‖ρ a * ρ b‖ ≤ K * K :=
    (norm_mul_le _ _).trans (mul_le_mul hRa hRb (norm_nonneg _) hK)
  have hsaP : ‖ρ (star a) * ρ (a * b)‖ ≤ K * K :=
    (norm_mul_le _ _).trans (mul_le_mul hRsa hRab (norm_nonneg _) hK)
  have hsaRR : ‖ρ (star a) * (ρ a * ρ b)‖ ≤ K * (K * K) :=
    (norm_mul_le _ _).trans (mul_le_mul hRsa hRaRb (norm_nonneg _) hK)
  have t1 : ‖ψ (ρ (star (a * b)) * ρ (a * b)) - star (a * b) * (a * b)‖
      ≤ δ * K + K * δ :=
    norm_bimod_step ρ ψ hsab hδ hsabK hRab hab
  have t2 : ‖ψ (ρ (star (a * b)) * (ρ a * ρ b)) - star (a * b) * (a * b)‖
      ≤ δ * (K * K) + K * (δ * K + K * δ) :=
    norm_bimod_step ρ ψ hsab hδ hsabK hRaRb e1
  have i3 : ‖ψ (ρ (star a) * ρ (a * b)) - star a * (a * b)‖ ≤ δ * K + K * δ :=
    norm_bimod_step ρ ψ hsa hδ hsaK hRab hab
  have t3 : ‖ψ (ρ (star b) * (ρ (star a) * ρ (a * b))) - star b * (star a * (a * b))‖
      ≤ δ * (K * K) + K * (δ * K + K * δ) :=
    norm_bimod_step ρ ψ hsb hδ hsbK hsaP i3
  have i4 : ‖ψ (ρ (star a) * (ρ a * ρ b)) - star a * (a * b)‖
      ≤ δ * (K * K) + K * (δ * K + K * δ) :=
    norm_bimod_step ρ ψ hsa hδ hsaK hRaRb e1
  have t4 : ‖ψ (ρ (star b) * (ρ (star a) * (ρ a * ρ b))) - star b * (star a * (a * b))‖
      ≤ δ * (K * (K * K)) + K * (δ * (K * K) + K * (δ * K + K * δ)) :=
    norm_bimod_step ρ ψ hsb hδ hsbK hsaRR i4
  have eD : star (ρ (a * b) - ρ a * ρ b) * (ρ (a * b) - ρ a * ρ b)
      = ρ (star (a * b)) * ρ (a * b) - ρ (star (a * b)) * (ρ a * ρ b)
        - ρ (star b) * (ρ (star a) * ρ (a * b))
        + ρ (star b) * (ρ (star a) * (ρ a * ρ b)) := by
    rw [hρs (a * b), hρs b, hρs a, star_sub, star_mul]
    simp only [sub_mul, mul_sub, mul_assoc]
    abel
  have eψ : ψ (star (ρ (a * b) - ρ a * ρ b) * (ρ (a * b) - ρ a * ρ b))
      = (ψ (ρ (star (a * b)) * ρ (a * b)) - star (a * b) * (a * b))
        - (ψ (ρ (star (a * b)) * (ρ a * ρ b)) - star (a * b) * (a * b))
        - (ψ (ρ (star b) * (ρ (star a) * ρ (a * b))) - star b * (star a * (a * b)))
        + (ψ (ρ (star b) * (ρ (star a) * (ρ a * ρ b))) - star b * (star a * (a * b))) := by
    rw [eD, map_add, map_sub, map_sub]
    abel
  rw [eψ]
  exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add ((norm_sub_le _ _).trans (add_le_add t1 t2)) t3)) t4)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.norm_psi_star_mul_defect_le

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
