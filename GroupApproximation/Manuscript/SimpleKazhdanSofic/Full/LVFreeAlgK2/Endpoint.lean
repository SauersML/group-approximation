import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFreeAlgK2.Augmented
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFieldK2.FieldK2
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFreeAlgGersten.Residual
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Morita
import GroupApproximation.Meta.AxiomGuard

/-!
# Stable `K₂(𝔽₂⟨x₀,x₁⟩) = 0` (lane LVNK1, WO-LVNK-1)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii, route W1.
Gersten, *K-theory of free rings*, Comm. Algebra 1 (1974): `K₂(F⟨X⟩) = K₂(F)`; with
`K₂(𝔽₂) = 0` (Steinberg 1962, lane LVFieldK2) this gives stable `K₂(𝔽₂⟨x₀,x₁⟩) = 0`, and by
Morita invariance the same for `M_m(𝔽₂⟨x₀,x₁⟩)` (the `B`-corner of the triangular pieces of
WO-LVNK-3).

CONDITIONAL on `LVFreeAlgGersten.skGer_PolyNilStatement` (`NK₂(𝔽₂⟨x₀,x₁⟩) = 0`, lane sk-ger-01).
The earlier unconditional version imported a module that was never written; it is replaced by
these conditional statements.  LOUD: the residual is a priori stronger than the Gersten nil part.
-/

namespace GroupApproximation.Full.LVFreeAlgK2

/-- **Stable `K₂(𝔽₂⟨x₀,x₁⟩) = 0`** from `NK₂(𝔽₂⟨x₀,x₁⟩) = 0` (Gersten 1974 plus `K₂(𝔽₂) = 0`).
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii, route W1.) -/
theorem stableK2Trivial_freeAlgebra_zmodTwo_of_polyNil
    (h : LVFreeAlgGersten.skGer_PolyNilStatement) :
    LVH2GL3.StableK2Trivial (FreeAlgebra (ZMod 2) (Fin 2)) :=
  (stableK2Trivial_freeAlgebra_iff (ZMod 2) (Fin 2)).mpr
    ⟨LVFieldK2.stableK2Trivial_zmodTwo,
      LVFreeAlgGersten.skGer_augNilK2Trivial_freeAlgebra_zmodTwo_of_polyNil h⟩

#audit_axioms GroupApproximation.Full.LVFreeAlgK2.stableK2Trivial_freeAlgebra_zmodTwo_of_polyNil

/-- Stable `K₂(M_m(𝔽₂⟨x₀,x₁⟩)) = 0` (Morita invariance), from `NK₂(𝔽₂⟨x₀,x₁⟩) = 0`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii, route W1.) -/
theorem stableK2Trivial_matrix_freeAlgebra_zmodTwo_of_polyNil
    (h : LVFreeAlgGersten.skGer_PolyNilStatement) (m : ℕ) :
    LVH2GL3.StableK2Trivial (Matrix (Fin m) (Fin m) (FreeAlgebra (ZMod 2) (Fin 2))) :=
  LVCohnK2.stableK2Trivial_matrix m (stableK2Trivial_freeAlgebra_zmodTwo_of_polyNil h)

#audit_axioms
  GroupApproximation.Full.LVFreeAlgK2.stableK2Trivial_matrix_freeAlgebra_zmodTwo_of_polyNil

end GroupApproximation.Full.LVFreeAlgK2
