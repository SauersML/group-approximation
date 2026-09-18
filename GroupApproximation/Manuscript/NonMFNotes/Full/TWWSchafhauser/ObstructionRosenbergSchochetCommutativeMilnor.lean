import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetLimOne

/-!
# The Milnor step for commutative algebras: algebra

Lane `TWWSch3d3-3C3`, work order `WO-TWWSchafhauser-3d3-3C` (section 3C3, commutative algebras
are detected by their boundary maps). Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378), through C. Schafhauser, J. reine angew. Math. 759
(2020), §§4--5, and J. Rosenberg, C. Schochet, Duke Math. J. 55 (1987), Prop. 1.8, Thm. 1.17.

Write a compact metrizable space as `X = lim Xₖ` with finite complexes `Xₖ`, so that
`C(X) = colim C(Xₖ)`. Milnor's `lim¹` sequence (J. Milnor, Pacific J. Math. 12 (1962);
C. Schochet, Pacific J. Math. 114 (1984)) says that a class `ξ ∈ Ext(C(X), J)` whose
restrictions to every `C(Xₖ)` vanish comes from the `lim¹` of the tower `Ext(S C(Xₖ), J)`, where
`lim¹` is the cokernel of `1 - shift` on the product. This file holds the algebra of that step.

* `Milnor.exists_telescope_of_bijective`: if a tower `Fₖ` is identified with `Hom(Gₖ, D)` by
  natural bijections, and `D` is divisible, then `1 - shift` is surjective on `∏ₖ Fₖ`, i.e.
  `lim¹ Fₖ = 0`. This transports `IsDivisibleGroup.exists_telescope_solution`.
* `Milnor.eq_zero_of_milnor`: if `ker (ξ ↦ (ρₖ ξ)ₖ)` lies in the image of a map `μ` which
  vanishes on the image of `1 - shift`, and `1 - shift` is surjective, then the `ρₖ` are jointly
  injective.
* `Milnor.eq_zero_of_milnor_of_divisible`: the two combined.
-/

namespace GroupApproximation.Full.TWWSchafhauser

universe u v w u₁ u₂

namespace Milnor

/-- **`lim¹` vanishes for towers of the form `Hom(Gₖ, D)`, `D` divisible.** Let
`sₖ : Fₖ₊₁ → Fₖ` be a tower and `θₖ : Fₖ ≅ Hom(Gₖ, D)` bijections that turn `sₖ` into
precomposition with `gₖ : Gₖ → Gₖ₊₁`. If `D` is divisible then every `(φₖ) ∈ ∏ Fₖ` is of the
form `ψₖ - sₖ ψₖ₊₁` (Rosenberg–Schochet, Duke Math. J. 55 (1987), Prop. 1.8). -/
theorem exists_telescope_of_bijective {D : Type u} [AddCommGroup D] (hD : IsDivisibleGroup D)
    {G : ℕ → Type v} [∀ k, AddCommGroup (G k)] (g : ∀ k, G k →+ G (k + 1))
    {F : ℕ → Type w} [∀ k, AddCommGroup (F k)] (s : ∀ k, F (k + 1) →+ F k)
    (θ : ∀ k, F k →+ (G k →+ D)) (hθ : ∀ k, Function.Bijective (θ k))
    (hnat : ∀ k (y : F (k + 1)), θ k (s k y) = (θ (k + 1) y).comp (g k))
    (φ : ∀ k, F k) : ∃ ψ : ∀ k, F k, ∀ k, ψ k - s k (ψ (k + 1)) = φ k := by
  obtain ⟨f, hf⟩ := hD.exists_telescope_solution g (fun k => θ k (φ k))
  refine ⟨fun k => (Equiv.ofBijective (θ k) (hθ k)).symm (f k), fun k => (hθ k).1 ?_⟩
  simp only [map_sub, hnat, Equiv.ofBijective_apply_symm_apply]
  exact hf k

/-- **The Milnor argument.** Let `ρₖ : E → E'ₖ` be restriction maps and `μ : ∏ₖ Fₖ → E` a map
whose image contains every `ξ` with all `ρₖ ξ = 0` and which kills the image of `1 - shift`.
If `1 - shift` is surjective on `∏ₖ Fₖ` (`lim¹ Fₖ = 0`), then `ξ = 0` as soon as every
`ρₖ ξ = 0`. -/
theorem eq_zero_of_milnor {E : Type u} [AddCommGroup E] {E' : ℕ → Type v}
    [∀ k, AddCommGroup (E' k)] (ρ : ∀ k, E →+ E' k) {F : ℕ → Type w} [∀ k, AddCommGroup (F k)]
    (s : ∀ k, F (k + 1) →+ F k) (μ : (∀ k, F k) → E)
    (hker : ∀ ξ : E, (∀ k, ρ k ξ = 0) → ∃ φ, μ φ = ξ)
    (hμ : ∀ ψ : ∀ k, F k, μ (fun k => ψ k - s k (ψ (k + 1))) = 0)
    (htel : ∀ φ : ∀ k, F k, ∃ ψ : ∀ k, F k, ∀ k, ψ k - s k (ψ (k + 1)) = φ k)
    (ξ : E) (hξ : ∀ k, ρ k ξ = 0) : ξ = 0 := by
  obtain ⟨φ, rfl⟩ := hker ξ hξ
  obtain ⟨ψ, hψ⟩ := htel φ
  have hφ : φ = fun k => ψ k - s k (ψ (k + 1)) := funext fun k => (hψ k).symm
  rw [hφ]
  exact hμ ψ

/-- **The Milnor argument with divisible coefficients.** In the situation of
`eq_zero_of_milnor`, the vanishing of `lim¹ Fₖ` is supplied by natural bijections
`Fₖ ≅ Hom(Gₖ, D)` with `D` divisible (`exists_telescope_of_bijective`). -/
theorem eq_zero_of_milnor_of_divisible {D : Type u₁} [AddCommGroup D] (hD : IsDivisibleGroup D)
    {G : ℕ → Type u₂} [∀ k, AddCommGroup (G k)] (g : ∀ k, G k →+ G (k + 1))
    {E : Type u} [AddCommGroup E] {E' : ℕ → Type v}
    [∀ k, AddCommGroup (E' k)] (ρ : ∀ k, E →+ E' k) {F : ℕ → Type w} [∀ k, AddCommGroup (F k)]
    (s : ∀ k, F (k + 1) →+ F k) (θ : ∀ k, F k →+ (G k →+ D))
    (hθ : ∀ k, Function.Bijective (θ k))
    (hnat : ∀ k (y : F (k + 1)), θ k (s k y) = (θ (k + 1) y).comp (g k))
    (μ : (∀ k, F k) → E)
    (hker : ∀ ξ : E, (∀ k, ρ k ξ = 0) → ∃ φ, μ φ = ξ)
    (hμ : ∀ ψ : ∀ k, F k, μ (fun k => ψ k - s k (ψ (k + 1))) = 0)
    (ξ : E) (hξ : ∀ k, ρ k ξ = 0) : ξ = 0 :=
  eq_zero_of_milnor ρ s μ hker hμ (exists_telescope_of_bijective hD g s θ hθ hnat) ξ hξ

end Milnor

end GroupApproximation.Full.TWWSchafhauser
