import GroupApproximation.BooneHigman.Metabelian.SuslinDilationAnalyticStatement
import GroupApproximation.BooneHigman.Metabelian.SuslinLocalGlobalCompose
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.AtPrime.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin local case, part 1: transition maps and eventual vanishing

Lane `bh-met-88`.  Clearing denominators from a localization `S = M⁻¹A` to some `A_a`.

For `a ∣ c` we have the transition map `A_a → A_c` (`suslinLocalCase_trans`), and for `a ∈ M`
the canonical map `A_a → S` (`suslinLocalCase_toLoc`).  The key fact is that an element of
`A_a` (resp. a polynomial, resp. an invertible polynomial matrix) that dies in `S` already dies
in `A_{a c}` for every `c` divisible by a suitable `b ∈ M`
(`suslinLocalCase_eventually_zero`, `suslinLocalCase_eventually_poly`,
`suslinLocalCase_eventually_units_eq`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

variable {A : Type*} [CommRing A]

/-- The transition map `A_a → A_c` for `a ∣ c`. -/
noncomputable def suslinLocalCase_trans {a c : A} (h : a ∣ c) :
    Localization.Away a →+* Localization.Away c :=
  IsLocalization.Away.lift a (IsLocalization.Away.isUnit_of_dvd (S := Localization.Away c) c h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_trans

theorem suslinLocalCase_trans_comp {a c : A} (h : a ∣ c) :
    (suslinLocalCase_trans h).comp (algebraMap A (Localization.Away a)) =
      algebraMap A (Localization.Away c) :=
  IsLocalization.Away.lift_comp a _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_trans_comp

theorem suslinLocalCase_trans_algebraMap {a c : A} (h : a ∣ c) (x : A) :
    suslinLocalCase_trans h (algebraMap A (Localization.Away a) x) =
      algebraMap A (Localization.Away c) x :=
  IsLocalization.Away.lift_eq a _ x

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_trans_algebraMap

/-- The canonical map `A_a → S` for a localization `S = M⁻¹A` and `a ∈ M`. -/
noncomputable def suslinLocalCase_toLoc (S : Type*) [CommRing S] [Algebra A S]
    {M : Submonoid A} [IsLocalization M S] {a : A} (ha : a ∈ M) :
    Localization.Away a →+* S :=
  IsLocalization.Away.lift a (IsLocalization.map_units (M := M) S ⟨a, ha⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_toLoc

theorem suslinLocalCase_toLoc_comp (S : Type*) [CommRing S] [Algebra A S]
    {M : Submonoid A} [IsLocalization M S] {a : A} (ha : a ∈ M) :
    (suslinLocalCase_toLoc S ha).comp (algebraMap A (Localization.Away a)) = algebraMap A S :=
  IsLocalization.Away.lift_comp a _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_toLoc_comp

theorem suslinLocalCase_toLoc_algebraMap (S : Type*) [CommRing S] [Algebra A S]
    {M : Submonoid A} [IsLocalization M S] {a : A} (ha : a ∈ M) (x : A) :
    suslinLocalCase_toLoc S ha (algebraMap A (Localization.Away a) x) = algebraMap A S x :=
  IsLocalization.Away.lift_eq a _ x

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_toLoc_algebraMap

/-- The canonical maps are compatible with the transition maps. -/
theorem suslinLocalCase_toLoc_comp_trans (S : Type*) [CommRing S] [Algebra A S]
    {M : Submonoid A} [IsLocalization M S] {a c : A} (ha : a ∈ M) (hc : c ∈ M) (h : a ∣ c) :
    (suslinLocalCase_toLoc S hc).comp (suslinLocalCase_trans h) = suslinLocalCase_toLoc S ha := by
  apply IsLocalization.ringHom_ext (Submonoid.powers a)
  rw [RingHom.comp_assoc, suslinLocalCase_trans_comp h, suslinLocalCase_toLoc_comp S hc,
    suslinLocalCase_toLoc_comp S ha]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_toLoc_comp_trans

/-- Functoriality of `elementaryMatrixUnitMap` for polynomial coefficient maps. -/
theorem suslinLocalCase_map_poly_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {N : ℕ} (f : S →+* T) (g : R →+* S)
    (u : Matrix.GeneralLinearGroup (Fin N) (Polynomial R)) :
    elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom f)
        (elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom g) u) =
      elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom (f.comp g)) u := by
  rw [suslinLocalGlobal_map_map, Polynomial.mapRingHom_comp]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_map_poly_comp

/-- Entries of the image of a polynomial matrix under a coefficient map. -/
theorem suslinLocalCase_entry {R T : Type*} [CommRing R] [CommRing T] {N : ℕ} (f : R →+* T)
    (u : Matrix.GeneralLinearGroup (Fin N) (Polynomial R)) (i j : Fin N) :
    (elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom f) u :
        Matrix (Fin N) (Fin N) (Polynomial T)) i j =
      Polynomial.map f ((u : Matrix (Fin N) (Fin N) (Polynomial R)) i j) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_entry

/-- Finitely many eventual properties hold eventually together. -/
theorem suslinLocalCase_eventually_finset (M : Submonoid A) {ι : Type*} (s : Finset ι)
    (P : ι → A → Prop) :
    (∀ i ∈ s, ∃ b ∈ M, ∀ c : A, b ∣ c → P i c) →
      ∃ b ∈ M, ∀ c : A, b ∣ c → ∀ i ∈ s, P i c := by
  classical
  induction s using Finset.induction_on with
  | empty => exact fun _ ↦ ⟨1, M.one_mem, fun _ _ i hi ↦ absurd hi (Finset.notMem_empty i)⟩
  | insert j s _ ih =>
    intro h
    obtain ⟨b, hb, hbP⟩ := h j (Finset.mem_insert_self j s)
    obtain ⟨b', hb', hb'P⟩ := ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
    refine ⟨b * b', M.mul_mem hb hb', fun c hc i hi ↦ ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi'
    · exact hbP c ((dvd_mul_right b b').trans hc)
    · exact hb'P c ((dvd_mul_left b' b).trans hc) i hi'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_eventually_finset

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
