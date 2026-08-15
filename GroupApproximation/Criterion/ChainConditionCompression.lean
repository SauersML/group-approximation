import GroupApproximation.Criterion.ExactCompression
import Mathlib.Order.OrderIsoNat

/-!
# Chain-condition invariants are blind to one-sided compression

`Criterion/FiniteQuotientBlindness` proves that a conjugation-invariant
size separating proper inclusions forbids strict one-sided compression.
This file drops the faithfulness hypothesis: an order isomorphism moving a
point of a chain-condition poset weakly in one direction fixes it.  The
compression reading takes the poset to be a lattice of invariants, the
isomorphism to be the action of one compressor, and the point to be the
invariant of the subgroup: an equivariant chain-condition invariant takes
the same value on `tΓt⁻¹` and on `Γ`, with no conclusion about the
subgroups themselves.

The finite-dimensional instance is `fixedSubmodule_conjugate_eq`: for
every finite-dimensional representation of the ambient group over every
field, the fixed subspace of the one-sided conjugate subgroup equals the
fixed subspace of the subgroup, as an equality of submodules.  Applied to
the induced representations on tensor constructions this is the
invariant-tensor rigidity printed by the manuscript; the commutant
identity behind Theorem `thm:B` is the `End(V)` case.
-/

namespace GroupApproximation

/-- **Ascending fixation.**  An order isomorphism moving a point up in a
poset with no infinite strictly ascending chain fixes it. -/
theorem orderIso_apply_eq_self_of_le_apply {P : Type*} [PartialOrder P]
    [hwf : WellFoundedGT P] (e : P ≃o P) {a : P} (ha : a ≤ e a) :
    e a = a := by
  set f : P → P := ⇑e with hf
  have hstep : ∀ n : ℕ, f^[n] a ≤ f^[n + 1] a := by
    intro n
    induction n with
    | zero => simpa using ha
    | succ n ih =>
        simp only [Function.iterate_succ_apply'] at ih ⊢
        exact e.monotone ih
  obtain ⟨x, ⟨n, rfl⟩, hmax⟩ := hwf.wf.has_min
    (Set.range fun n : ℕ ↦ f^[n] a) (Set.range_nonempty _)
  have hnot : ¬ f^[n] a < f^[n + 1] a := hmax _ ⟨n + 1, rfl⟩
  have hfix : f^[n] a = f^[n + 1] a :=
    ((hstep n).lt_or_eq).resolve_left hnot
  have hiter : f^[n] (f a) = f^[n] a := by
    rw [← Function.iterate_succ_apply]
    exact hfix.symm
  have hinj : Function.Injective f := e.toEquiv.injective
  exact hinj.iterate n hiter

/-- **Descending fixation.**  An order isomorphism moving a point down in
a poset with no infinite strictly descending chain fixes it. -/
theorem orderIso_apply_eq_self_of_apply_le {P : Type*} [PartialOrder P]
    [hwf : WellFoundedLT P] (e : P ≃o P) {a : P} (ha : e a ≤ a) :
    e a = a := by
  set f : P → P := ⇑e with hf
  have hstep : ∀ n : ℕ, f^[n + 1] a ≤ f^[n] a := by
    intro n
    induction n with
    | zero => simpa using ha
    | succ n ih =>
        simp only [Function.iterate_succ_apply'] at ih ⊢
        exact e.monotone ih
  obtain ⟨x, ⟨n, rfl⟩, hmin⟩ := hwf.wf.has_min
    (Set.range fun n : ℕ ↦ f^[n] a) (Set.range_nonempty _)
  have hnot : ¬ f^[n + 1] a < f^[n] a := hmin _ ⟨n + 1, rfl⟩
  have hfix : f^[n + 1] a = f^[n] a :=
    ((hstep n).lt_or_eq).resolve_left hnot
  have hiter : f^[n] (f a) = f^[n] a := by
    rw [← Function.iterate_succ_apply]
    exact hfix
  have hinj : Function.Injective f := e.toEquiv.injective
  exact hinj.iterate n hiter

section Linear

variable {G : Type*} [Group G] {k V : Type*} [Field k] [AddCommGroup V]
  [Module k V]

/-- **Fixed subspaces do not see one-sided compression**, as an equality
of submodules: for every finite-dimensional representation of the ambient
group, the one-sided conjugate subgroup has the same fixed subspace as the
subgroup itself. -/
theorem fixedSubmodule_conjugate_eq [FiniteDimensional k V]
    (σ : G →* (V ≃ₗ[k] V)) (Γ : Subgroup G) {t : G}
    (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) :
    fixedSubmodule σ (Subgroup.map (MulAut.conj t).toMonoidHom Γ) =
      fixedSubmodule σ Γ := by
  ext v
  have hiff := fixedSubmodule_compressed_eq σ Γ ht v
  constructor
  · intro hv
    refine hiff.mp fun γ hγ ↦ ?_
    have hx := (mem_fixedSubmodule.mp hv) ((MulAut.conj t).toMonoidHom γ)
      (Subgroup.mem_map_of_mem _ hγ)
    simpa [MulAut.conj_apply] using hx
  · intro hv
    rw [mem_fixedSubmodule]
    rintro x ⟨γ, hγ, rfl⟩
    simpa [MulAut.conj_apply] using hiff.mpr hv γ hγ

end Linear

universe u v

/-- Closed form of the chain-condition compression-blindness principle,
with the fixed-subspace instance printed by the manuscript: ascending and
descending fixation for order isomorphisms, and the equality of fixed
subspaces of a subgroup and its one-sided conjugate in every
finite-dimensional representation over every field. -/
theorem manuscriptChainConditionRigidity :
    (∀ (P : Type u) [PartialOrder P] [WellFoundedGT P] (e : P ≃o P)
      (a : P), a ≤ e a → e a = a) ∧
      (∀ (P : Type u) [PartialOrder P] [WellFoundedLT P] (e : P ≃o P)
        (a : P), e a ≤ a → e a = a) ∧
      (∀ (G : Type u) [Group G] (k V : Type v) [Field k] [AddCommGroup V]
        [Module k V] [FiniteDimensional k V] (σ : G →* (V ≃ₗ[k] V))
        (Γ : Subgroup G) (t : G), (∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) →
          fixedSubmodule σ (Subgroup.map (MulAut.conj t).toMonoidHom Γ) =
            fixedSubmodule σ Γ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro P _ _ e a ha
    exact orderIso_apply_eq_self_of_le_apply e ha
  · intro P _ _ e a ha
    exact orderIso_apply_eq_self_of_apply_le e ha
  · intro G _ k V _ _ _ _ σ Γ t ht
    exact fixedSubmodule_conjugate_eq σ Γ ht

end GroupApproximation
