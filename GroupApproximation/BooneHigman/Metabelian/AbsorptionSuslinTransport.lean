import GroupApproximation.BooneHigman.Metabelian.AbsorptionEndpoint
import GroupApproximation.KOne.FieldKOneDeterminant
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin input, part 1: transport, the zero ring and fields

Lane `bh-met-23`.  `AbsorptionEndpoint.lean` reduces both chain absorption statements to
`PolynomialSuslinStatement`, a statement about `SpecialLinearInElementary R N` (every
determinant-one invertible `N × N` matrix over `R` is elementary).  This file proves the
three soft facts the induction on the number of variables needs:

* `specialLinearInElementary_of_ringEquiv`: the property transports along a ring isomorphism
  (conjugate by `Matrix.map e.symm`, use `RingEquiv.map_det`, push the elementary group forward
  with `elementaryGroup_map_le`);
* `specialLinearInElementary_of_subsingleton`: over the zero ring (e.g. `ℤ[1/0]`) there is only
  one matrix;
* `specialLinearInElementary_of_field`: over a field at every positive rank, from the tree's
  Gaussian elimination `AlgebraicK.mem_elementaryGroup_of_detUnits_eq_one`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **Transport along a ring isomorphism.** -/
theorem specialLinearInElementary_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {N : ℕ} (h : SpecialLinearInElementary R N) :
    SpecialLinearInElementary S N := by
  intro u hu
  let v : Matrix.GeneralLinearGroup (Fin N) R :=
    elementaryMatrixUnitMap (ι := Fin N) e.symm.toRingHom u
  have hvval : (v : Matrix (Fin N) (Fin N) R) =
      e.symm.toRingHom.mapMatrix (u : Matrix (Fin N) (Fin N) S) := rfl
  have hv : Matrix.det (v : Matrix (Fin N) (Fin N) R) = 1 := by
    rw [hvval, ← RingHom.map_det, hu, map_one]
  have hmem : elementaryMatrixUnitMap (ι := Fin N) e.toRingHom v ∈ elementaryGroup (Fin N) S :=
    elementaryGroup_map_le e.toRingHom (Subgroup.mem_map_of_mem _ (h v hv))
  have hback : elementaryMatrixUnitMap (ι := Fin N) e.toRingHom v = u := by
    apply Units.ext
    ext i j
    change e (e.symm ((u : Matrix (Fin N) (Fin N) S) i j)) = (u : Matrix (Fin N) (Fin N) S) i j
    exact e.apply_symm_apply _
  rw [hback] at hmem
  exact hmem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.specialLinearInElementary_of_ringEquiv

/-- Transport along a ring isomorphism, as an equivalence. -/
theorem specialLinearInElementary_congr {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (N : ℕ) : SpecialLinearInElementary R N ↔ SpecialLinearInElementary S N :=
  ⟨specialLinearInElementary_of_ringEquiv e, specialLinearInElementary_of_ringEquiv e.symm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.specialLinearInElementary_congr

/-- **The zero ring.**  Every matrix over a subsingleton ring is the identity. -/
theorem specialLinearInElementary_of_subsingleton (R : Type*) [CommRing R] [Subsingleton R]
    (N : ℕ) : SpecialLinearInElementary R N := by
  intro u _
  have hu : u = 1 := Units.ext (Subsingleton.elim _ _)
  rw [hu]
  exact one_mem _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.specialLinearInElementary_of_subsingleton

/-- **Fields.**  Over a field, `SL_N = E_N` at every positive rank (Gaussian elimination). -/
theorem specialLinearInElementary_of_field (K : Type*) [Field K] {N : ℕ} (hN : 0 < N) :
    SpecialLinearInElementary K N := by
  intro u hu
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  refine AlgebraicK.mem_elementaryGroup_of_detUnits_eq_one ?_
  apply Units.ext
  rw [AlgebraicK.detUnits_val, Units.val_one]
  exact hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.specialLinearInElementary_of_field

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
