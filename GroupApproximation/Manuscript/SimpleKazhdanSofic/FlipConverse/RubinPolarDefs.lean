import Mathlib
import GroupApproximation.Meta.AxiomGuard

/-!
# Rubin polars, part 1: the rigid-polar predicate and its invariance under isomorphisms

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"), lane
`sk-flip-16` of the flip-converse region (Rubin route).  Pure group theory.

For a group `G`, a subgroup `P`, and `g : G`:

* `rubinConjSubgroup g P` is the conjugate subgroup `g P g⁻¹ = {x | g⁻¹ x g ∈ P}`.
* `rubinTransport Φ P` is the image `Φ '' P` of `P` under an isomorphism `Φ : G ≃* H`, written as
  the preimage under `Φ.symm`.
* `IsRigidPolar P` (with `C` the centraliser):
  `P = C(C P)`, `P ⊓ C P = ⊥`, `∀ g, P ⊓ gPg⁻¹ ≠ ⊥ ∨ gPg⁻¹ ≤ C P`, and
  `∀ g, C P ⊓ g(C P)g⁻¹ ≠ ⊥ ∨ g(C P)g⁻¹ ≤ P`.

`isRigidPolar_rubinTransport`: the predicate is invariant under isomorphisms.  `Φ` carries
centralisers to centralisers (`rubinTransport_centralizer`), conjugates to conjugates
(`rubinConjSubgroup_rubinTransport`), meets to meets, `⊥` to `⊥`, and preserves `≤`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

section RubinPolarGroup

variable {G H : Type*} [Group G] [Group H]

/-- The conjugate subgroup `g P g⁻¹`. -/
def rubinConjSubgroup (g : G) (P : Subgroup G) : Subgroup G :=
  P.comap (MulAut.conj g).symm.toMonoidHom

theorem mem_rubinConjSubgroup {g x : G} {P : Subgroup G} :
    x ∈ rubinConjSubgroup g P ↔ g⁻¹ * x * g ∈ P :=
  Iff.rfl

/-- The image of a subgroup under an isomorphism, as the preimage under the inverse. -/
def rubinTransport (Φ : G ≃* H) (P : Subgroup G) : Subgroup H :=
  P.comap Φ.symm.toMonoidHom

theorem mem_rubinTransport {Φ : G ≃* H} {P : Subgroup G} {k : H} :
    k ∈ rubinTransport Φ P ↔ Φ.symm k ∈ P :=
  Iff.rfl

/-- The rigid-polar predicate of lane `sk-flip-16`. -/
def IsRigidPolar (P : Subgroup G) : Prop :=
  P = Subgroup.centralizer (Subgroup.centralizer (P : Set G) : Set G) ∧
    P ⊓ Subgroup.centralizer (P : Set G) = ⊥ ∧
    (∀ g : G, P ⊓ rubinConjSubgroup g P ≠ ⊥ ∨
      rubinConjSubgroup g P ≤ Subgroup.centralizer (P : Set G)) ∧
    ∀ g : G, Subgroup.centralizer (P : Set G) ⊓
        rubinConjSubgroup g (Subgroup.centralizer (P : Set G)) ≠ ⊥ ∨
      rubinConjSubgroup g (Subgroup.centralizer (P : Set G)) ≤ P

theorem rubinTransport_centralizer (Φ : G ≃* H) (P : Subgroup G) :
    Subgroup.centralizer (rubinTransport Φ P : Set H) =
      rubinTransport Φ (Subgroup.centralizer (P : Set G)) := by
  ext k
  rw [mem_rubinTransport, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hk x hx
    have hx' : Φ x ∈ (rubinTransport Φ P : Set H) := by
      show Φ.symm (Φ x) ∈ P
      rw [MulEquiv.symm_apply_apply]
      exact hx
    have h1 : Φ x * k = k * Φ x := hk (Φ x) hx'
    apply Φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h1
  · intro hk y hy
    have hy' : Φ.symm y ∈ P := hy
    have h1 : Φ.symm y * Φ.symm k = Φ.symm k * Φ.symm y := hk (Φ.symm y) hy'
    apply Φ.symm.injective
    rw [map_mul, map_mul]
    exact h1

theorem rubinConjSubgroup_rubinTransport (Φ : G ≃* H) (k : H) (P : Subgroup G) :
    rubinConjSubgroup k (rubinTransport Φ P) =
      rubinTransport Φ (rubinConjSubgroup (Φ.symm k) P) := by
  ext x
  rw [mem_rubinConjSubgroup, mem_rubinTransport, mem_rubinTransport, mem_rubinConjSubgroup,
    map_mul, map_mul, map_inv]

theorem rubinTransport_eq_bot_iff (Φ : G ≃* H) (P : Subgroup G) :
    rubinTransport Φ P = ⊥ ↔ P = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall, Subgroup.eq_bot_iff_forall]
  constructor
  · intro h x hx
    have hx' : Φ x ∈ rubinTransport Φ P := by
      show Φ.symm (Φ x) ∈ P
      rw [MulEquiv.symm_apply_apply]
      exact hx
    have h1 : Φ x = Φ 1 := by
      rw [map_one]
      exact h (Φ x) hx'
    exact Φ.injective h1
  · intro h y hy
    have h1 : Φ.symm y = Φ.symm 1 := by
      rw [map_one]
      exact h (Φ.symm y) hy
    exact Φ.symm.injective h1

theorem rubinTransport_inf (Φ : G ≃* H) (A B : Subgroup G) :
    rubinTransport Φ A ⊓ rubinTransport Φ B = rubinTransport Φ (A ⊓ B) := by
  ext x
  rw [Subgroup.mem_inf, mem_rubinTransport, mem_rubinTransport, mem_rubinTransport,
    Subgroup.mem_inf]

theorem rubinTransport_mono (Φ : G ≃* H) {A B : Subgroup G} (h : A ≤ B) :
    rubinTransport Φ A ≤ rubinTransport Φ B :=
  fun _ hk => h hk

/-- The rigid-polar predicate is invariant under group isomorphisms. -/
theorem isRigidPolar_rubinTransport (Φ : G ≃* H) {P : Subgroup G} (hP : IsRigidPolar P) :
    IsRigidPolar (rubinTransport Φ P) := by
  obtain ⟨h1, h2, h3, h4⟩ := hP
  refine ⟨?_, ?_, fun k => ?_, fun k => ?_⟩
  · rw [rubinTransport_centralizer, rubinTransport_centralizer, ← h1]
  · rw [rubinTransport_centralizer, rubinTransport_inf, h2, rubinTransport_eq_bot_iff]
  · rw [rubinTransport_centralizer, rubinConjSubgroup_rubinTransport, rubinTransport_inf, ne_eq,
      rubinTransport_eq_bot_iff]
    rcases h3 (Φ.symm k) with h | h
    · exact Or.inl h
    · exact Or.inr (rubinTransport_mono Φ h)
  · rw [rubinTransport_centralizer, rubinConjSubgroup_rubinTransport, rubinTransport_inf, ne_eq,
      rubinTransport_eq_bot_iff]
    rcases h4 (Φ.symm k) with h | h
    · exact Or.inl h
    · exact Or.inr (rubinTransport_mono Φ h)

end RubinPolarGroup

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinConjSubgroup
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.mem_rubinConjSubgroup
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinTransport
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.mem_rubinTransport
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.IsRigidPolar
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinTransport_centralizer
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinConjSubgroup_rubinTransport
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinTransport_eq_bot_iff
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinTransport_inf
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinTransport_mono
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.isRigidPolar_rubinTransport
