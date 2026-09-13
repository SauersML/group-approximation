import GroupApproximation.KirchbergPhillips.IntertwiningLimit
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Approximate unitary equivalence and Elliott's intertwining theorem

Two unital ⋆-homomorphisms `ρ σ : A →⋆ₐ[ℂ] B` are approximately unitarily equivalent when every
finite set is moved within any `ε` of `σ` by conjugating `ρ` with a unitary of `B`.

**Elliott's intertwining theorem.** Let `A` and `B` be separable unital C⋆-algebras. If
`ρ : A → B` and `σ : B → A` are unital ⋆-homomorphisms with `σ ∘ ρ ≈ᵤ id` and `ρ ∘ σ ≈ᵤ id`, then
`A ≃⋆ₐ[ℂ] B` (`nonempty_starAlgEquiv_of_approxUnitarilyEquivalent`).

The proof builds `α n = Ad uₙ ∘ ρ` and `β n = Ad vₙ ∘ σ` with finite sets `F n ⊆ A`, `G n ⊆ B` and
errors `2⁻ⁿ` (`exists_intertwining_data`), then passes to the limit with
`nonempty_starAlgEquiv_of_tendsto`.

## Main definitions

* `conjHom u ρ`: `x ↦ u ρ(x) u⋆`.
* `ApproxUnitarilyEquivalent ρ σ`.
-/

open Filter Topology TopologicalSpace

namespace GroupApproximation

namespace KirchbergPhillips

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- `x ↦ u ρ(x) u⋆`: `ρ` followed by the inner automorphism of the unitary `u`. -/
noncomputable def conjHom (u : unitary B) (ρ : A →⋆ₐ[ℂ] B) : A →⋆ₐ[ℂ] B :=
  (Unitary.conjStarAlgAut ℂ B u).toStarAlgHom.comp ρ

@[simp] theorem conjHom_apply (u : unitary B) (ρ : A →⋆ₐ[ℂ] B) (x : A) :
    conjHom u ρ x = (u : B) * ρ x * star (u : B) := rfl

/-- `ρ` and `σ` are approximately unitarily equivalent: for every finite set `F` and `ε > 0` there is
a unitary `u` with `‖u ρ(x) u⋆ - σ(x)‖ < ε` for `x ∈ F`. -/
def ApproxUnitarilyEquivalent (ρ σ : A →⋆ₐ[ℂ] B) : Prop :=
  ∀ F : Finset A, ∀ ε : ℝ, 0 < ε →
    ∃ u : unitary B, ∀ x ∈ F, ‖(u : B) * ρ x * star (u : B) - σ x‖ < ε

theorem ApproxUnitarilyEquivalent.refl (ρ : A →⋆ₐ[ℂ] B) : ApproxUnitarilyEquivalent ρ ρ :=
  fun _ _ hε => ⟨1, fun x _ => by
    show ‖(1 : B) * ρ x * star (1 : B) - ρ x‖ < _
    rw [one_mul, star_one, mul_one, sub_self, norm_zero]
    exact hε⟩

theorem ApproxUnitarilyEquivalent.symm {ρ σ : A →⋆ₐ[ℂ] B} (h : ApproxUnitarilyEquivalent ρ σ) :
    ApproxUnitarilyEquivalent σ ρ := by
  intro F ε hε
  obtain ⟨u, hu⟩ := h F ε hε
  refine ⟨star u, fun x hx => ?_⟩
  have key : ((star u : unitary B) : B) * σ x * star ((star u : unitary B) : B) - ρ x =
      star (u : B) * (σ x - (u : B) * ρ x * star (u : B)) * (u : B) := by
    simp only [Unitary.coe_star, star_star, mul_sub, sub_mul, mul_assoc]
    simp only [← mul_assoc (star (u : B)) (u : B), Unitary.star_mul_self_of_mem u.2, one_mul,
      mul_one]
  rw [key, CStarRing.norm_mul_coe_unitary, CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem u.2),
    norm_sub_rev]
  exact hu x hx

/-- If `σ ∘ ρ ≈ᵤ id`, then for every unitary `u` of `B`, `σ ∘ Ad u ∘ ρ` is conjugated within `ε` of the
identity on a finite set by a unitary of `A`. -/
theorem exists_unitary_conj_comp_conj (ρ : A →⋆ₐ[ℂ] B) (σ : B →⋆ₐ[ℂ] A)
    (h : ApproxUnitarilyEquivalent (σ.comp ρ) (StarAlgHom.id ℂ A)) (u : unitary B) (F : Finset A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : unitary A, ∀ x ∈ F,
      ‖(v : A) * σ ((u : B) * ρ x * star (u : B)) * star (v : A) - x‖ < ε := by
  obtain ⟨w, hw⟩ := h F ε hε
  have hu : σ (u : B) ∈ unitary A := Unitary.map_mem σ u.2
  refine ⟨w * star ⟨σ (u : B), hu⟩, fun x hx => ?_⟩
  have hv : ((w * star ⟨σ (u : B), hu⟩ : unitary A) : A) = (w : A) * star (σ (u : B)) := rfl
  have h1 : star (σ (u : B)) * σ (u : B) = 1 := Unitary.star_mul_self_of_mem hu
  rw [hv]
  simp only [map_mul, map_star, star_mul, star_star, mul_assoc]
  simp only [← mul_assoc (star (σ (u : B))) (σ (u : B)), h1, one_mul]
  have key := hw x hx
  rw [mul_assoc] at key
  exact key

/-- The data of an approximate intertwining: `α n = Ad uₙ ∘ ρ`, `β n = Ad vₙ ∘ σ`, finite sets `F n`,
`G n` containing the first terms of the sequences `a`, `b`, with zig-zag errors below `2⁻ⁿ`. -/
theorem exists_intertwining_data (ρ : A →⋆ₐ[ℂ] B) (σ : B →⋆ₐ[ℂ] A)
    (hσρ : ApproxUnitarilyEquivalent (σ.comp ρ) (StarAlgHom.id ℂ A))
    (hρσ : ApproxUnitarilyEquivalent (ρ.comp σ) (StarAlgHom.id ℂ B)) (a : ℕ → A) (b : ℕ → B) :
    ∃ (α : ℕ → A →⋆ₐ[ℂ] B) (β : ℕ → B →⋆ₐ[ℂ] A) (F : ℕ → Finset A) (G : ℕ → Finset B),
      (∀ n, ∀ x ∈ F n, ‖β n (α n x) - x‖ < (1 / 2 : ℝ) ^ n) ∧
      (∀ n, ∀ y ∈ G n, ‖α (n + 1) (β n y) - y‖ < (1 / 2 : ℝ) ^ n) ∧
      (∀ n, ∀ x ∈ F n, α n x ∈ G n) ∧ (∀ n, ∀ y ∈ G n, β n y ∈ F (n + 1)) ∧
      (∀ n k, k ≤ n → a k ∈ F n) ∧ (∀ n k, k ≤ n → b k ∈ G n) := by
  classical
  have hpos : ∀ n : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ n := fun n => pow_pos (by norm_num) n
  choose V hV using fun (n : ℕ) (u : unitary B) (F : Finset A) =>
    exists_unitary_conj_comp_conj ρ σ hσρ u F (hpos n)
  choose U hU using fun (n : ℕ) (v : unitary A) (G : Finset B) =>
    exists_unitary_conj_comp_conj σ ρ hρσ v G (hpos n)
  obtain ⟨Gs, hGs⟩ : ∃ Gs : ℕ → unitary B → Finset A → Finset B, ∀ n u F,
      Gs n u F = F.image (conjHom u ρ) ∪ (Finset.range (n + 1)).image b :=
    ⟨fun n u F => F.image (conjHom u ρ) ∪ (Finset.range (n + 1)).image b, fun _ _ _ => rfl⟩
  obtain ⟨st, hst0, hstS⟩ : ∃ st : ℕ → unitary B × Finset A,
      st 0 = (1, (Finset.range 1).image a) ∧
      ∀ n, st (n + 1) = (U n (V n (st n).1 (st n).2) (Gs n (st n).1 (st n).2),
        (Gs n (st n).1 (st n).2).image (conjHom (V n (st n).1 (st n).2) σ) ∪
          (Finset.range (n + 2)).image a) :=
    ⟨fun n => Nat.rec (motive := fun _ => unitary B × Finset A) (1, (Finset.range 1).image a)
      (fun n s => (U n (V n s.1 s.2) (Gs n s.1 s.2),
        (Gs n s.1 s.2).image (conjHom (V n s.1 s.2) σ) ∪ (Finset.range (n + 2)).image a)) n,
      rfl, fun _ => rfl⟩
  refine ⟨fun n => conjHom (st n).1 ρ, fun n => conjHom (V n (st n).1 (st n).2) σ,
    fun n => (st n).2, fun n => Gs n (st n).1 (st n).2, fun n x hx => ?_, fun n y hy => ?_,
    fun n x hx => ?_, fun n y hy => ?_, fun n k hk => ?_, fun n k hk => ?_⟩
  · simpa only [conjHom_apply] using hV n (st n).1 (st n).2 x hx
  · simpa only [conjHom_apply, hstS n] using
      hU n (V n (st n).1 (st n).2) (Gs n (st n).1 (st n).2) y hy
  · simp only [hGs]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)
  · simp only [hstS n]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy)
  · cases n with
    | zero =>
      simp only [hst0]
      exact Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega))
    | succ n =>
      simp only [hstS n]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega)))
  · simp only [hGs]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega)))

/-- **Elliott's intertwining theorem.** Separable unital C⋆-algebras `A`, `B` with unital
⋆-homomorphisms `ρ : A → B`, `σ : B → A` such that `σ ∘ ρ ≈ᵤ id` and `ρ ∘ σ ≈ᵤ id` are isomorphic. -/
theorem nonempty_starAlgEquiv_of_approxUnitarilyEquivalent [SeparableSpace A] [SeparableSpace B]
    (ρ : A →⋆ₐ[ℂ] B) (σ : B →⋆ₐ[ℂ] A)
    (hσρ : ApproxUnitarilyEquivalent (σ.comp ρ) (StarAlgHom.id ℂ A))
    (hρσ : ApproxUnitarilyEquivalent (ρ.comp σ) (StarAlgHom.id ℂ B)) : Nonempty (A ≃⋆ₐ[ℂ] B) := by
  have : Nonempty A := ⟨0⟩
  have : Nonempty B := ⟨0⟩
  obtain ⟨α, β, _F, _G, h1, h2, h3, h4, h5, h6⟩ :=
    exists_intertwining_data ρ σ hσρ hρσ (denseSeq A) (denseSeq B)
  refine nonempty_starAlgEquiv_of_tendsto α β (denseRange_denseSeq A) (denseRange_denseSeq B)
    (fun k => cauchySeq_of_dist_succ_le k fun n hn => ?_)
    (fun k => cauchySeq_of_dist_succ_le k fun n hn => ?_)
    (fun k => tendsto_of_dist_le_half_pow k fun n hn => ?_)
    (fun k => tendsto_of_dist_le_half_pow k fun n hn => ?_)
  · have hx := h5 n k hn
    calc dist (α n (denseSeq A k)) (α (n + 1) (denseSeq A k))
        ≤ dist (α n (denseSeq A k)) (α (n + 1) (β n (α n (denseSeq A k)))) +
            dist (α (n + 1) (β n (α n (denseSeq A k)))) (α (n + 1) (denseSeq A k)) :=
          dist_triangle _ _ _
      _ ≤ (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ n := by
          refine add_le_add ?_ ((dist_apply_le _ _ _).trans ?_)
          · rw [dist_comm, dist_eq_norm]
            exact (h2 n _ (h3 n _ hx)).le
          · rw [dist_eq_norm]
            exact (h1 n _ hx).le
      _ = 2 * (1 / 2 : ℝ) ^ n := by ring
  · have hy := h6 n k hn
    calc dist (β n (denseSeq B k)) (β (n + 1) (denseSeq B k))
        ≤ dist (β n (denseSeq B k)) (β (n + 1) (α (n + 1) (β n (denseSeq B k)))) +
            dist (β (n + 1) (α (n + 1) (β n (denseSeq B k)))) (β (n + 1) (denseSeq B k)) :=
          dist_triangle _ _ _
      _ ≤ (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ n := by
          refine add_le_add ?_ ((dist_apply_le _ _ _).trans ?_)
          · rw [dist_comm, dist_eq_norm]
            exact (h1 (n + 1) _ (h4 n _ hy)).le.trans
              (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right n 1))
          · rw [dist_eq_norm]
            exact (h2 n _ hy).le
      _ = 2 * (1 / 2 : ℝ) ^ n := by ring
  · rw [dist_eq_norm]
    exact (h1 n _ (h5 n k hn)).le
  · rw [dist_eq_norm]
    exact (h2 n _ (h6 n k hn)).le

end KirchbergPhillips

end GroupApproximation
