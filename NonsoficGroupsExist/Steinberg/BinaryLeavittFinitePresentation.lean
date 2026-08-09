import NonsoficGroupsExist.Steinberg.FinitePresentationReduction
import NonsoficGroupsExist.Leavitt.FinitePresentation

/-!
# Finite-presentation reduction for the binary-Leavitt Steinberg group

This module isolates the exact formal interface to the free-ring theorem of
Krstić--McCool.  The absolute six-relation presentation of
`L_{𝔽₂}(1,2)` and the passage from coefficient-ring relations to normally
generated Steinberg relations are proved internally.  What remains explicit
as a hypothesis is finite presentability over a free associative ring.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavittSteinberg

/-- Finite presentability of `St_n(L_{𝔽₂}(1,2))`, reduced exactly to the
free-associative-ring case of the Krstić--McCool theorem. -/
theorem finitelyPresented_of_freeRing
    {n : ℕ} (hn : 3 ≤ n)
    (hfree : ∀ m : ℕ,
      Group.IsFinitelyPresented
        (SteinbergGroup (Fin n) (FreeAlgebra ℤ (Fin m)))) :
    Group.IsFinitelyPresented
      (SteinbergGroup (Fin n)
        (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) := by
  exact SteinbergGroup.isFinitelyPresented_of_isFinitelyPresentedNC
    (I := Fin n) (S := BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))
    (by simpa using hn) hfree

end BinaryLeavittSteinberg
end NonsoficGroupsExist
