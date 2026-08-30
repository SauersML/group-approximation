import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic

/-!
# Finite-quotient Fell untwisting retains a kernel cocycle

Tensoring a representation of a group `G` with the left-regular
representation of a finite quotient `Q` does not make the `G`-representation
disappear.  After the usual section-dependent change of basis, the residual
block at quotient coordinate `a` is the representation of

`s(q(g) a)⁻¹ g s(a)`.

This file isolates the algebraic content of that calculation.  Finiteness of
`Q`, unitarity of the representation, and a choice of Hilbert space are not
needed for the identity itself, so the declarations are stated for arbitrary
groups and an arbitrary target group `U`.  In the finite unitary case they
are exactly the block formula used by the Fell basis change.
-/

namespace GroupApproximation
namespace FiniteQuotientFellCocycle

variable {G Q U : Type*} [Group G] [Group Q] [Group U]

/-- The section cocycle associated to `q : G → Q` and a section `s`:
`c(g,a) = s(q(g)a)⁻¹ g s(a)`. -/
def cocycle (q : G →* Q) (s : Q → G) (g : G) (a : Q) : G :=
  (s (q g * a))⁻¹ * g * s a

/-- If `s` is a section of `q`, every value of the section cocycle lies in
the kernel of `q`. -/
theorem cocycle_mem_ker (q : G →* Q) (s : Q → G)
    (hs : ∀ a, q (s a) = a) (g : G) (a : Q) :
    cocycle q s g a ∈ q.ker := by
  change q (cocycle q s g a) = 1
  simp only [cocycle, map_mul, map_inv, hs]
  group

/-- The section cocycle obeys the left-translation cocycle law
`c(gh,a) = c(g,q(h)a)c(h,a)`. -/
theorem cocycle_mul (q : G →* Q) (s : Q → G) (g h : G) (a : Q) :
    cocycle q s (g * h) a = cocycle q s g (q h * a) * cocycle q s h a := by
  have hqa : q (g * h) * a = q g * (q h * a) := by
    rw [map_mul, mul_assoc]
  simp only [cocycle, hqa]
  group

/-- The fibre identity behind finite-quotient Fell untwisting.  If `π` is
the original representation, conjugating the `g`-block from fibre `a` to
fibre `q(g)a` replaces `π(g)` by `π(c(g,a))`. -/
theorem block_conjugation (q : G →* Q) (s : Q → G) (π : G →* U)
    (g : G) (a : Q) :
    (π (s (q g * a)))⁻¹ * π g * π (s a) = π (cocycle q s g a) := by
  simp [cocycle]

/-- On a fixed block, the untwisted operator is a pure quotient permutation
exactly when the represented kernel-cocycle value is trivial. -/
theorem block_is_pure_iff (q : G →* Q) (s : Q → G) (π : G →* U)
    (g : G) (a : Q) :
    (π (s (q g * a)))⁻¹ * π g * π (s a) = 1 ↔
      π (cocycle q s g a) = 1 := by
  rw [block_conjugation]

/-- If the representation factors through the quotient, every residual
section-cocycle block is killed. -/
theorem cocycle_killed_of_factors (q : G →* Q) (s : Q → G)
    (hs : ∀ a, q (s a) = a) (ρ : Q →* U) (g : G) (a : Q) :
    (ρ.comp q) (cocycle q s g a) = 1 := by
  have hc := cocycle_mem_ker q s hs g a
  change q (cocycle q s g a) = 1 at hc
  change ρ (q (cocycle q s g a)) = 1
  simp [hc]

end FiniteQuotientFellCocycle
end GroupApproximation
