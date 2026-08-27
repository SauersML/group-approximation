import GroupApproximation.Higman.OmegaTower
import GroupApproximation.Higman.EnumeratedRangeTrace

/-!
# The Omega block alphabet is the standard window relation

The tower calls its local alphabet `blockSet m`, while the reified arithmetic
calculus calls the same set `windowSupport m`.  Identifying them lets the
Omega benignness side consume the already reified window construction instead
of maintaining a second code path.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open Seq

/-- Sequences supported on the Omega block `[0,m)` are exactly the standard
arity-`m` window-supported sequences. -/
theorem blockSet_eq_windowSupport (m : ℕ) :
    blockSet m = windowSupport m := by
  ext f
  constructor
  · intro hf
    rw [mem_windowSupport_iff]
    constructor
    · intro i hi
      apply hf i
      rw [Finset.mem_Ico]
      omega
    · intro i hi
      apply hf i
      rw [Finset.mem_Ico]
      omega
  · intro hf i hi
    obtain ⟨hneg, hupper⟩ := (mem_windowSupport_iff m f).mp hf
    by_cases h0 : i < 0
    · exact hneg i h0
    · apply hupper i
      rw [Finset.mem_Ico] at hi
      omega

/-- The selected alphabet can be normalized to the common window name in the
Omega operation identity. -/
theorem omegaOp_inter_windowSupport (m : ℕ) (B : Set E) :
    omegaOp m (B ∩ windowSupport m) = omegaOp m B := by
  rw [← blockSet_eq_windowSupport m]
  exact omegaOp_inter_blockSet m B

end Omega
end Higman
end GroupApproximation
