import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFreeAlgK2.Augmented
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFieldK2.FieldK2
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFreeAlgGersten.Endpoint
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Morita

/-!
# Stable `K₂(𝔽₂⟨x₀,x₁⟩) = 0` (lane LVNK1, WO-LVNK-1)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii, route W1.
Gersten, *K-theory of free rings*, Comm. Algebra 1 (1974): `K₂(F⟨X⟩) = K₂(F)`; with
`K₂(𝔽₂) = 0` (Steinberg 1962, lane LVFieldK2) this gives stable `K₂(𝔽₂⟨x₀,x₁⟩) = 0`, and by
Morita invariance the same for `M_m(𝔽₂⟨x₀,x₁⟩)` (the `B`-corner of the triangular pieces of
WO-LVNK-3).
-/

namespace GroupApproximation.Full.LVFreeAlgK2

/-- **Stable `K₂(𝔽₂⟨x₀,x₁⟩) = 0`** (Gersten 1974 plus `K₂(𝔽₂) = 0`).
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii, route W1.) -/
theorem stableK2Trivial_freeAlgebra_zmodTwo :
    LVH2GL3.StableK2Trivial (FreeAlgebra (ZMod 2) (Fin 2)) :=
  (stableK2Trivial_freeAlgebra_iff (ZMod 2) (Fin 2)).mpr
    ⟨LVFieldK2.stableK2Trivial_zmodTwo, LVFreeAlgGersten.augNilK2Trivial_freeAlgebra_zmodTwo⟩

/-- Stable `K₂(M_m(𝔽₂⟨x₀,x₁⟩)) = 0` (Morita invariance).
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii, route W1.) -/
theorem stableK2Trivial_matrix_freeAlgebra_zmodTwo (m : ℕ) :
    LVH2GL3.StableK2Trivial (Matrix (Fin m) (Fin m) (FreeAlgebra (ZMod 2) (Fin 2))) :=
  LVCohnK2.stableK2Trivial_matrix m stableK2Trivial_freeAlgebra_zmodTwo

end GroupApproximation.Full.LVFreeAlgK2
