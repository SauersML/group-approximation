import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFreeAlgGersten.Retract
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFreeAlgGersten.Deformation
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFreeAlgK2.ZModTwo
import GroupApproximation.Meta.AxiomGuard

/-!
# Gersten nil part of `K₂(𝔽₂⟨x₀,x₁⟩)`: reduction to `NK₂` (lane sk-ger-01)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii, route W1.

The target `augNilK2Trivial_freeAlgebra_zmodTwo`, i.e.
`AugNilK2Trivial (freeAug (ZMod 2) (Fin 2))`, is **not** closed here, and
`LVFreeAlgGersten.Endpoint` is deliberately **not** created.

What is proved (no literature inputs):

* `skGer_augNil_of_retract` (`Retract`): nil parts of stable `K₂` pass to retract squares;
* the scaling deformation `ψ : F⟨V⟩ → F⟨V⟩[t]`, `xᵢ ↦ xᵢ t`, with `(t ↦ 0) ∘ ψ = const ∘ aug`
  and `(t ↦ 1) ∘ ψ = id` (`Deformation`);
* hence (`skGer_augNil_freeAlgebra_of_polyNil`) for every commutative `F` and every `V`:
  the Gersten nil part of `F⟨V⟩` vanishes as soon as `NK₂(F⟨V⟩)` does, i.e. as soon as
  `AugNilK2Trivial (constantCoeff : F⟨V⟩[t] → F⟨V⟩)`.

The single remaining Statement is `skGer_PolyNilStatement`: `NK₂(𝔽₂⟨x₀,x₁⟩) = 0`.

**Truth.** TRUE: `𝔽₂⟨x₀,x₁⟩` is a free ideal ring, hence regular coherent, hence `K`-regular
(`NKₙ = 0`; Gersten 1974, Waldhausen 1978).

**LOUD — strength.** This Statement is **not strictly weaker** than the target: it is a priori
**stronger**.  By the deformation, the target's nil part is a direct summand of `NK₂(𝔽₂⟨x₀,x₁⟩)`
(`skGer_augNilK2Trivial_freeAlgebra_zmodTwo_of_polyNil`), and no converse is available.  It also
contains the commutative polynomial nil part `NK₂(𝔽₂) = 0` (`skGer_polyNilZModTwo_of_polyNil`).
It is not Prop-equivalent (by any proof we have) to `AugNilK2Trivial (freeAug …)`, to stable
`K₂(𝔽₂⟨x₀,x₁⟩) = 0`, or to the Cohn degree-zero / graded-generation statements.  We found no
natural statement that is both strictly weaker and still implies the target: special cases of
the target, and graded-generation reformulations, are either implied by the target outright
(hence equivalent once the `_of_` reduction is proved) or on the AVOID list.  It is **smaller in
proof content** only in one sense: the noncommutative augmentation bookkeeping is gone, and what
remains is the classical homotopy-invariance input `NK₂ = 0` for a free algebra.
-/

namespace GroupApproximation.Full.LVFreeAlgGersten

/-- **Deformation reduction.**  For every commutative `F` and every `V`, `NK₂(F⟨V⟩) = 0`
(the nil part of `t ↦ 0 : F⟨V⟩[t] → F⟨V⟩`) implies vanishing of the Gersten nil part of
`aug : F⟨V⟩ → F`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii, route W1.) -/
theorem skGer_augNil_freeAlgebra_of_polyNil (F V : Type*) [CommRing F]
    (h : LVFreeAlgK2.AugNilK2Trivial (Polynomial.constantCoeff (R := FreeAlgebra F V))) :
    LVFreeAlgK2.AugNilK2Trivial (LVFreeAlgK2.freeAug F V) :=
  skGer_augNil_of_retract (Polynomial.constantCoeff (R := FreeAlgebra F V))
    (LVFreeAlgK2.freeAug F V) (skGer_deform F V) (skGer_evalOne (FreeAlgebra F V))
    (LVFreeAlgK2.freeConst F V) (skGer_evalOne_comp_deform F V)
    (skGer_constantCoeff_comp_deform F V) h

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_augNil_freeAlgebra_of_polyNil

/-- **Residual Statement** (TRUE; LOUD: a priori *stronger* than the target, see the module
docstring): `NK₂(𝔽₂⟨x₀,x₁⟩) = 0`, the nil part of stable `K₂` for
`t ↦ 0 : 𝔽₂⟨x₀,x₁⟩[t] → 𝔽₂⟨x₀,x₁⟩`.
(Gersten 1974; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii, route W1.) -/
def skGer_PolyNilStatement : Prop :=
  LVFreeAlgK2.AugNilK2Trivial (Polynomial.constantCoeff (R := FreeAlgebra (ZMod 2) (Fin 2)))

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_PolyNilStatement

/-- **Target from the residual**: `NK₂(𝔽₂⟨x₀,x₁⟩) = 0` kills the Gersten nil part.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii, route W1.) -/
theorem skGer_augNilK2Trivial_freeAlgebra_zmodTwo_of_polyNil (h : skGer_PolyNilStatement) :
    LVFreeAlgK2.AugNilK2Trivial (LVFreeAlgK2.freeAug (ZMod 2) (Fin 2)) :=
  skGer_augNil_freeAlgebra_of_polyNil (ZMod 2) (Fin 2) h

#audit_axioms
  GroupApproximation.Full.LVFreeAlgGersten.skGer_augNilK2Trivial_freeAlgebra_zmodTwo_of_polyNil

/-- Stable `K₂(𝔽₂⟨x₀,x₁⟩) = 0` from the residual (via `stableK2Trivial_freeAlgebra_zmodTwo_iff`,
which uses `K₂(𝔽₂) = 0`).
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii, route W1.) -/
theorem skGer_stableK2Trivial_freeAlgebra_zmodTwo_of_polyNil (h : skGer_PolyNilStatement) :
    LVH2GL3.StableK2Trivial (FreeAlgebra (ZMod 2) (Fin 2)) :=
  (LVFreeAlgK2.stableK2Trivial_freeAlgebra_zmodTwo_iff (Fin 2)).mpr
    (skGer_augNilK2Trivial_freeAlgebra_zmodTwo_of_polyNil h)

#audit_axioms
  GroupApproximation.Full.LVFreeAlgGersten.skGer_stableK2Trivial_freeAlgebra_zmodTwo_of_polyNil

/-- LOUD scope witness: the residual also contains the commutative polynomial nil part
`NK₂(𝔽₂) = 0` (nil part of `t ↦ 0 : 𝔽₂[t] → 𝔽₂`), a retract along coefficientwise constants.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii, route W1.) -/
theorem skGer_polyNilZModTwo_of_polyNil (h : skGer_PolyNilStatement) :
    LVFreeAlgK2.AugNilK2Trivial (Polynomial.constantCoeff (R := ZMod 2)) :=
  skGer_augNil_of_retract (Polynomial.constantCoeff (R := FreeAlgebra (ZMod 2) (Fin 2)))
    (Polynomial.constantCoeff (R := ZMod 2))
    (Polynomial.mapRingHom (LVFreeAlgK2.freeConst (ZMod 2) (Fin 2)))
    (Polynomial.mapRingHom (LVFreeAlgK2.freeAug (ZMod 2) (Fin 2)))
    (LVFreeAlgK2.freeConst (ZMod 2) (Fin 2))
    (skGer_mapFreeAug_comp_mapFreeConst (ZMod 2) (Fin 2))
    (skGer_constantCoeff_comp_mapFreeConst (ZMod 2) (Fin 2)) h

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_polyNilZModTwo_of_polyNil

end GroupApproximation.Full.LVFreeAlgGersten
