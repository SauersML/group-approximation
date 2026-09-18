import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Units.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Group-theoretic helpers for `St_4(ℤ[1/m])` f.p. (bh-met-91m)

* `czStFourFP_isFinitelyPresented_of_retract`: if a finitely presented group `P` has
  homomorphisms `φ : P → G`, `ψ : G → P` with `φ ∘ ψ = id`, then `G` is finitely presented
  (the kernel of `φ` is the normal closure of the finitely many elements `aᵢ⁻¹ ψ(φ(aᵢ))`).
* `czStFourFP_conj_pow_iter`, `czStFourFP_conj_zpow_iter`: iterating a conjugation rule
  `g f(r) g⁻¹ = f(c r)`.
* `czStFourFP_commute_of_commute_of`: an element commuting with all generators of a presented
  group is central.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

/-- The finite normal generating set of the kernel of a retraction. -/
def czStFourFP_retractSet {α : Type*} {rels : Set (FreeGroup α)} {G : Type*} [Group G]
    (φ : PresentedGroup rels →* G) (ψ : G →* PresentedGroup rels) :
    Set (PresentedGroup rels) :=
  Set.range fun a : α => (PresentedGroup.of a)⁻¹ * ψ (φ (PresentedGroup.of a))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_retractSet

/-- **Retract criterion.**  A retract (through `φ ∘ ψ = id`) of a finite presentation is
finitely presented. -/
theorem czStFourFP_isFinitelyPresented_of_retract {α : Type*} [Finite α]
    {rels : Set (FreeGroup α)} [Finite rels] {G : Type*} [Group G]
    (φ : PresentedGroup rels →* G) (ψ : G →* PresentedGroup rels)
    (h : ∀ g, φ (ψ g) = g) : Group.IsFinitelyPresented G := by
  refine Group.IsFinitelyPresented.of_surjective φ (fun g => ⟨ψ g, h g⟩)
    ⟨czStFourFP_retractSet φ ψ, Set.finite_range _, ?_⟩
  apply le_antisymm
  · refine Subgroup.normalClosure_le_normal (Set.range_subset_iff.mpr fun a => ?_)
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  · intro g hg
    have hq : (QuotientGroup.mk' (Subgroup.normalClosure (czStFourFP_retractSet φ ψ))).comp
        (ψ.comp φ) = QuotientGroup.mk' (Subgroup.normalClosure (czStFourFP_retractSet φ ψ)) := by
      apply PresentedGroup.ext
      intro a
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq]
      exact Subgroup.subset_normalClosure ⟨a, rfl⟩
    have h1 := DFunLike.congr_fun hq g
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hg, map_one, map_one,
      QuotientGroup.mk'_apply] at h1
    exact (QuotientGroup.eq_one_iff g).mp h1.symm

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_isFinitelyPresented_of_retract

/-- Iterating a conjugation rule `g f(r) g⁻¹ = f(c r)` (natural powers). -/
theorem czStFourFP_conj_pow_iter {G R : Type*} [Group G] [Monoid R] {g : G} {f : R → G}
    {c : R} (hg : ∀ r, g * f r * g⁻¹ = f (c * r)) (n : ℕ) (r : R) :
    g ^ n * f r * (g ^ n)⁻¹ = f (c ^ n * r) := by
  induction n generalizing r with
  | zero => simp only [pow_zero, one_mul, inv_one, mul_one]
  | succ n ih =>
    calc g ^ (n + 1) * f r * (g ^ (n + 1))⁻¹ = g ^ n * (g * f r * g⁻¹) * (g ^ n)⁻¹ := by
          rw [pow_succ, mul_inv_rev]; simp only [mul_assoc]
      _ = f (c ^ (n + 1) * r) := by rw [hg, ih, pow_succ, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_conj_pow_iter

/-- Iterating a conjugation rule `g f(r) g⁻¹ = f(c r)` with `c` a unit (integer powers). -/
theorem czStFourFP_conj_zpow_iter {G R : Type*} [Group G] [Monoid R] {g : G} {f : R → G}
    {c : Rˣ} (hg : ∀ r, g * f r * g⁻¹ = f ((c : R) * r)) (j : ℤ) (r : R) :
    g ^ j * f r * (g ^ j)⁻¹ = f (((c ^ j : Rˣ) : R) * r) := by
  have hinv : ∀ r, g⁻¹ * f r * g⁻¹⁻¹ = f (((c⁻¹ : Rˣ) : R) * r) := by
    intro r
    have h := hg (((c⁻¹ : Rˣ) : R) * r)
    rw [← mul_assoc (c : R), Units.mul_inv, one_mul] at h
    rw [← h]
    simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · rw [zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
    exact czStFourFP_conj_pow_iter hg n r
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow, ← inv_pow,
      Units.val_pow_eq_pow_val]
    exact czStFourFP_conj_pow_iter hinv n r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_conj_zpow_iter

/-- An element commuting with every generator of a presented group is central. -/
theorem czStFourFP_commute_of_commute_of {α : Type*} {rels : Set (FreeGroup α)}
    {z : PresentedGroup rels}
    (hz : ∀ a : α, PresentedGroup.of a * z = z * PresentedGroup.of a)
    (g : PresentedGroup rels) : g * z = z * g := by
  have hmem : g ∈ Subgroup.centralizer {z} :=
    PresentedGroup.generated_by rels _ (fun a => Subgroup.mem_centralizer_iff.mpr
      fun h hh => by rw [Set.mem_singleton_iff.mp hh]; exact (hz a).symm) g
  exact (Subgroup.mem_centralizer_iff.mp hmem z (Set.mem_singleton z)).symm

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_commute_of_commute_of

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
