import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Finset.Insert
import GroupApproximation.Meta.AxiomGuard

/-!
# Transposition presentations of finite symmetric groups (lane bh-met-77c)

Let `t : α → α → G` be a family of elements of a group indexed by ordered pairs of a finite
type with decidable equality, such that

* `t a a = 1`,
* `t a b * t a b = 1`,
* `t a b * t c e * (t a b)⁻¹ = t (swap a b c) (swap a b e)`.

Then the map `FreeGroup (α × α) → G` sending `(a, b)` to `t a b` kills every word whose image
under `(a, b) ↦ swap a b` in `Equiv.Perm α` is trivial (`higmanVCAll_lift_eq_one`).

This is shown with a *section*: a map `ψ : Equiv.Perm α → G` with `ψ 1 = 1` and
`ψ (swap a b * σ) = t a b * ψ σ` (`higmanVCAll_permSection`).  It is built by induction on a
finite support set `S`: to add a point `z ∉ S`, put
`ψ' σ = t (σ z) z * ψ (swap (σ z) z * σ)` (`higmanVCAll_ext`).  Here `swap (σ z) z * σ` fixes
`z` and is supported in `S`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

section PermSection

variable {α : Type*} [DecidableEq α] {G : Type*} [Group G]

/-- The relators force each `t a b` to be its own inverse. -/
theorem higmanVCAll_t_inv (t : α → α → G) (h2 : ∀ a b, t a b * t a b = 1) (a b : α) :
    (t a b)⁻¹ = t a b :=
  inv_eq_of_mul_eq_one_right (h2 a b)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_t_inv

/-- The conjugation relator written as a commutation rule. -/
theorem higmanVCAll_t_conj (t : α → α → G)
    (h3 : ∀ a b c e, t a b * t c e * (t a b)⁻¹ = t (Equiv.swap a b c) (Equiv.swap a b e))
    (a b c e : α) :
    t a b * t c e = t (Equiv.swap a b c) (Equiv.swap a b e) * t a b := by
  rw [← h3 a b c e, inv_mul_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_t_conj

/-- The conjugation relator forces the symmetry `t a b = t b a`. -/
theorem higmanVCAll_t_symm (t : α → α → G)
    (h3 : ∀ a b c e, t a b * t c e * (t a b)⁻¹ = t (Equiv.swap a b c) (Equiv.swap a b e))
    (a b : α) : t a b = t b a := by
  have h := h3 a b a b
  rw [mul_inv_cancel_right, Equiv.swap_apply_left, Equiv.swap_apply_right] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_t_symm

/-- The trivial transposition `swap a a` acts trivially by left multiplication. -/
theorem higmanVCAll_swap_self_mul (a : α) (σ : Equiv.Perm α) : Equiv.swap a a * σ = σ :=
  Equiv.ext fun x => by rw [Equiv.Perm.mul_apply, Equiv.swap_self, Equiv.refl_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_swap_self_mul

/-- Conjugating a transposition by a transposition. -/
theorem higmanVCAll_swap_conj (a b c e : α) :
    Equiv.swap (Equiv.swap a b c) (Equiv.swap a b e) * Equiv.swap a b =
      Equiv.swap a b * Equiv.swap c e := by
  rw [Equiv.swap_apply_apply (Equiv.swap a b) c e, inv_mul_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_swap_conj

/-- If `σ` is supported in `insert z S` then `swap (σ z) z * σ` is supported in `S`. -/
theorem higmanVCAll_supp_step {S : Finset α} {z : α} {σ : Equiv.Perm α}
    (hσ : ∀ x, x ∉ insert z S → σ x = x) :
    ∀ x, x ∉ S → (Equiv.swap (σ z) z * σ) x = x := by
  intro x hx
  rw [Equiv.Perm.mul_apply]
  by_cases hxz : x = z
  · rw [hxz]
    exact Equiv.swap_apply_left _ _
  · have hxi : x ∉ insert z S := by
      rw [Finset.mem_insert]
      exact fun h => h.elim hxz hx
    rw [hσ x hxi]
    refine Equiv.swap_apply_of_ne_of_ne (fun h => hxz (σ.injective ?_)) hxz
    rw [hσ x hxi]
    exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_supp_step

/-- If `σ` is supported in `insert z S` and moves `z`, then `σ z ∈ S`. -/
theorem higmanVCAll_mem_of_supp {S : Finset α} {z : α} {σ : Equiv.Perm α}
    (hσ : ∀ x, x ∉ insert z S → σ x = x) (hcz : σ z ≠ z) : σ z ∈ S := by
  by_contra h
  have hi : σ z ∉ insert z S := by
    rw [Finset.mem_insert]
    exact fun h' => h'.elim hcz h
  exact hcz (σ.injective (hσ _ hi))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_mem_of_supp

/-- The extension of a partial section across one new point `z`. -/
def higmanVCAll_ext (t : α → α → G) (z : α) (ψ : Equiv.Perm α → G) (σ : Equiv.Perm α) : G :=
  t (σ z) z * ψ (Equiv.swap (σ z) z * σ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_ext

/-- The extension step for a transposition `swap a b` with `a, b ∈ S`. -/
theorem higmanVCAll_step_away (t : α → α → G)
    (h3 : ∀ a b c e, t a b * t c e * (t a b)⁻¹ = t (Equiv.swap a b c) (Equiv.swap a b e))
    {S : Finset α} {z : α} (hz : z ∉ S) (ψ : Equiv.Perm α → G)
    (hψ : ∀ a ∈ S, ∀ b ∈ S, ∀ σ : Equiv.Perm α, (∀ x, x ∉ S → σ x = x) →
      ψ (Equiv.swap a b * σ) = t a b * ψ σ)
    {a b : α} (ha : a ∈ S) (hb : b ∈ S) {σ : Equiv.Perm α}
    (hσ : ∀ x, x ∉ insert z S → σ x = x) :
    higmanVCAll_ext t z ψ (Equiv.swap a b * σ) = t a b * higmanVCAll_ext t z ψ σ := by
  have hfix : Equiv.swap a b z = z :=
    Equiv.swap_apply_of_ne_of_ne (fun h => hz (by rw [h]; exact ha))
      (fun h => hz (by rw [h]; exact hb))
  have hp : Equiv.swap (Equiv.swap a b (σ z)) z * Equiv.swap a b =
      Equiv.swap a b * Equiv.swap (σ z) z := by
    rw [← higmanVCAll_swap_conj a b (σ z) z, hfix]
  have hg : t a b * t (σ z) z = t (Equiv.swap a b (σ z)) z * t a b := by
    rw [higmanVCAll_t_conj t h3 a b (σ z) z, hfix]
  simp only [higmanVCAll_ext, Equiv.Perm.mul_apply]
  rw [← mul_assoc (Equiv.swap (Equiv.swap a b (σ z)) z), hp, mul_assoc (Equiv.swap a b),
    hψ a ha b hb _ (higmanVCAll_supp_step hσ), ← mul_assoc, ← mul_assoc, hg]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_step_away

/-- The extension step for a transposition `swap a z` with `a ∈ S`. -/
theorem higmanVCAll_step_at (t : α → α → G) (h1 : ∀ a, t a a = 1)
    (h2 : ∀ a b, t a b * t a b = 1)
    (h3 : ∀ a b c e, t a b * t c e * (t a b)⁻¹ = t (Equiv.swap a b c) (Equiv.swap a b e))
    {S : Finset α} {z : α} (hz : z ∉ S) (ψ : Equiv.Perm α → G)
    (hψ : ∀ a ∈ S, ∀ b ∈ S, ∀ σ : Equiv.Perm α, (∀ x, x ∉ S → σ x = x) →
      ψ (Equiv.swap a b * σ) = t a b * ψ σ)
    {a : α} (ha : a ∈ S) {σ : Equiv.Perm α}
    (hσ : ∀ x, x ∉ insert z S → σ x = x) :
    higmanVCAll_ext t z ψ (Equiv.swap a z * σ) = t a z * higmanVCAll_ext t z ψ σ := by
  have haz : a ≠ z := fun h => hz (by rw [← h]; exact ha)
  by_cases hcz : σ z = z
  · simp only [higmanVCAll_ext, Equiv.Perm.mul_apply]
    rw [hcz, Equiv.swap_apply_right, Equiv.swap_mul_self_mul, h1, one_mul,
      higmanVCAll_swap_self_mul]
  by_cases hca : σ z = a
  · simp only [higmanVCAll_ext, Equiv.Perm.mul_apply]
    rw [hca, Equiv.swap_apply_left, h1, one_mul, higmanVCAll_swap_self_mul, ← mul_assoc, h2,
      one_mul]
  have hac : a ≠ σ z := fun h => hca h.symm
  have hfa : Equiv.swap (σ z) z a = a := Equiv.swap_apply_of_ne_of_ne hac haz
  have hfc : Equiv.swap a z (σ z) = σ z := Equiv.swap_apply_of_ne_of_ne hca hcz
  have hp : Equiv.swap (σ z) z * Equiv.swap a z =
      Equiv.swap a (σ z) * Equiv.swap (σ z) z := by
    rw [← higmanVCAll_swap_conj (σ z) z a z, hfa, Equiv.swap_apply_right]
  have hg : t (σ z) z * t a (σ z) = t a z * t (σ z) z := by
    rw [higmanVCAll_t_conj t h3 (σ z) z a (σ z), hfa, Equiv.swap_apply_left]
  simp only [higmanVCAll_ext, Equiv.Perm.mul_apply]
  rw [hfc, ← mul_assoc (Equiv.swap (σ z) z), hp, mul_assoc (Equiv.swap a (σ z)),
    hψ a ha (σ z) (higmanVCAll_mem_of_supp hσ hcz) _ (higmanVCAll_supp_step hσ), ← mul_assoc,
    hg, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_step_at

/-- The extension step for an arbitrary transposition supported in `insert z S`. -/
theorem higmanVCAll_step (t : α → α → G) (h1 : ∀ a, t a a = 1)
    (h2 : ∀ a b, t a b * t a b = 1)
    (h3 : ∀ a b c e, t a b * t c e * (t a b)⁻¹ = t (Equiv.swap a b c) (Equiv.swap a b e))
    {S : Finset α} {z : α} (hz : z ∉ S) (ψ : Equiv.Perm α → G)
    (hψ : ∀ a ∈ S, ∀ b ∈ S, ∀ σ : Equiv.Perm α, (∀ x, x ∉ S → σ x = x) →
      ψ (Equiv.swap a b * σ) = t a b * ψ σ)
    {a b : α} (ha : a ∈ insert z S) (hb : b ∈ insert z S) {σ : Equiv.Perm α}
    (hσ : ∀ x, x ∉ insert z S → σ x = x) :
    higmanVCAll_ext t z ψ (Equiv.swap a b * σ) = t a b * higmanVCAll_ext t z ψ σ := by
  by_cases hab : a = b
  · rw [hab, higmanVCAll_swap_self_mul, h1, one_mul]
  rcases Finset.mem_insert.mp ha with haz | ha'
  · rcases Finset.mem_insert.mp hb with hbz | hb'
    · exact absurd (haz.trans hbz.symm) hab
    · rw [haz, Equiv.swap_comm, higmanVCAll_t_symm t h3 z b]
      exact higmanVCAll_step_at t h1 h2 h3 hz ψ hψ hb' hσ
  · rcases Finset.mem_insert.mp hb with hbz | hb'
    · rw [hbz]
      exact higmanVCAll_step_at t h1 h2 h3 hz ψ hψ ha' hσ
    · exact higmanVCAll_step_away t h3 hz ψ hψ ha' hb' hσ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_step

/-- **Partial sections.**  For every finite set `S` there is `ψ` with `ψ 1 = 1` and
`ψ (swap a b * σ) = t a b * ψ σ` for `a, b ∈ S` and `σ` supported in `S`. -/
theorem higmanVCAll_permSection_finset (t : α → α → G) (h1 : ∀ a, t a a = 1)
    (h2 : ∀ a b, t a b * t a b = 1)
    (h3 : ∀ a b c e, t a b * t c e * (t a b)⁻¹ = t (Equiv.swap a b c) (Equiv.swap a b e))
    (S : Finset α) :
    ∃ ψ : Equiv.Perm α → G, ψ 1 = 1 ∧ ∀ a ∈ S, ∀ b ∈ S, ∀ σ : Equiv.Perm α,
      (∀ x, x ∉ S → σ x = x) → ψ (Equiv.swap a b * σ) = t a b * ψ σ := by
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 1, rfl, fun a ha => absurd ha (Finset.notMem_empty a)⟩
  | insert z S hz ih =>
    obtain ⟨ψ, hψ1, hψ⟩ := ih
    refine ⟨higmanVCAll_ext t z ψ, ?_, fun a ha b hb σ hσ =>
      higmanVCAll_step t h1 h2 h3 hz ψ hψ ha hb hσ⟩
    rw [higmanVCAll_ext, Equiv.Perm.one_apply, h1, one_mul, higmanVCAll_swap_self_mul, hψ1]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_permSection_finset

/-- **Sections.**  On a finite type there is `ψ : Equiv.Perm α → G` with `ψ 1 = 1` and
`ψ (swap a b * σ) = t a b * ψ σ` for all `a, b, σ`. -/
theorem higmanVCAll_permSection [Fintype α] (t : α → α → G) (h1 : ∀ a, t a a = 1)
    (h2 : ∀ a b, t a b * t a b = 1)
    (h3 : ∀ a b c e, t a b * t c e * (t a b)⁻¹ = t (Equiv.swap a b c) (Equiv.swap a b e)) :
    ∃ ψ : Equiv.Perm α → G, ψ 1 = 1 ∧ ∀ (a b : α) (σ : Equiv.Perm α),
      ψ (Equiv.swap a b * σ) = t a b * ψ σ := by
  obtain ⟨ψ, hψ1, hψ⟩ := higmanVCAll_permSection_finset t h1 h2 h3 Finset.univ
  exact ⟨ψ, hψ1, fun a b σ => hψ a (Finset.mem_univ a) b (Finset.mem_univ b) σ
    fun x hx => absurd (Finset.mem_univ x) hx⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_permSection

/-- A section intertwines the two evaluations of a word in the free group on pairs. -/
theorem higmanVCAll_section_word (t : α → α → G) (h2 : ∀ a b, t a b * t a b = 1)
    (ψ : Equiv.Perm α → G) (hψ : ∀ (a b : α) (σ : Equiv.Perm α),
      ψ (Equiv.swap a b * σ) = t a b * ψ σ) (r : FreeGroup (α × α)) :
    ∀ σ : Equiv.Perm α,
      ψ (FreeGroup.lift (fun p : α × α => Equiv.swap p.1 p.2) r * σ) =
        FreeGroup.lift (fun p : α × α => t p.1 p.2) r * ψ σ := by
  induction r using FreeGroup.induction_on with
  | C1 =>
    intro σ
    simp only [map_one, one_mul]
  | of x =>
    intro σ
    simp only [FreeGroup.lift_apply_of]
    exact hψ x.1 x.2 σ
  | inv_of x _ =>
    intro σ
    simp only [map_inv, FreeGroup.lift_apply_of, Equiv.swap_inv, higmanVCAll_t_inv t h2]
    exact hψ x.1 x.2 σ
  | mul x y hx hy =>
    intro σ
    rw [map_mul, map_mul, mul_assoc, hx, hy, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_section_word

/-- **Transposition presentation.**  A word whose transposition image is trivial is killed by
`(a, b) ↦ t a b`. -/
theorem higmanVCAll_lift_eq_one [Fintype α] (t : α → α → G) (h1 : ∀ a, t a a = 1)
    (h2 : ∀ a b, t a b * t a b = 1)
    (h3 : ∀ a b c e, t a b * t c e * (t a b)⁻¹ = t (Equiv.swap a b c) (Equiv.swap a b e))
    (r : FreeGroup (α × α))
    (hr : FreeGroup.lift (fun p : α × α => Equiv.swap p.1 p.2) r = 1) :
    FreeGroup.lift (fun p : α × α => t p.1 p.2) r = 1 := by
  obtain ⟨ψ, hψ1, hψ⟩ := higmanVCAll_permSection t h1 h2 h3
  have h := higmanVCAll_section_word t h2 ψ hψ r 1
  rw [hr, one_mul, hψ1, mul_one] at h
  exact h.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_lift_eq_one

end PermSection

end GroupApproximation.BooneHigman.Metabelian.Envelope
