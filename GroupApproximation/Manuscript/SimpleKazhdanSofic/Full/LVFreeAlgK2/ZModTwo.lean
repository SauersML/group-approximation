import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFreeAlgK2.Augmented
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFieldK2.FieldK2

/-!
# Stable `K₂(𝔽₂⟨X⟩) = 0` is exactly the Gersten nil part (lane LVNK1, WO-LVNK-1)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii, route W1.
With stable `K₂(𝔽₂) = 0` (Steinberg 1962; lane LVFieldK2, `stableK2Trivial_zmodTwo`), the
splitting `stableK2Trivial_freeAlgebra_iff` reduces stable `K₂(𝔽₂⟨X⟩) = 0` to, and makes it
equivalent to, vanishing of the augmentation nil part (Gersten, *K-theory of free rings*,
Comm. Algebra 1 (1974)).
-/

namespace GroupApproximation.Full.LVFreeAlgK2

/-- Stable `K₂(𝔽₂⟨X⟩) = 0` iff the augmentation nil part of `K₂(𝔽₂⟨X⟩)` vanishes.
(Gersten 1974; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii, route W1.) -/
theorem stableK2Trivial_freeAlgebra_zmodTwo_iff (X : Type*) :
    LVH2GL3.StableK2Trivial (FreeAlgebra (ZMod 2) X) ↔
      AugNilK2Trivial (freeAug (ZMod 2) X) :=
  (stableK2Trivial_freeAlgebra_iff (ZMod 2) X).trans
    (and_iff_right LVFieldK2.stableK2Trivial_zmodTwo)

end GroupApproximation.Full.LVFreeAlgK2
