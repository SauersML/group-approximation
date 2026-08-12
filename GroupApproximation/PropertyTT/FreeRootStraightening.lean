import GroupApproximation.PropertyT.FreeRootFiltration
import GroupApproximation.PropertyTT.LocallyFiniteStraightening

/-!
# Exact cocycle straightening on characteristic-two free roots

The degree filtration of an elementary root over a finite free algebra is
an exhaustive chain of finite subgroups.  Hence the general weak-averaging
construction applies without any amenability or rigidity assumption.
-/

namespace GroupApproximation
namespace FreeRootStraightening

open FreeRootFiltration
open scoped InnerProductSpace

noncomputable section

universe v

variable (X : Type*) [Fintype X]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

abbrev G := elementaryGroup (Fin 3) (FreeAlgebra (ZMod 2) X)

/-- The finite degree stages concretely exhaust one full elementary root. -/
theorem exhausts_rootDegreeSubgroup (i j : Fin 3) (hij : i ≠ j) :
    ExhaustsSubgroup (elementaryRootSubgroup i j hij)
      (rootDegreeSubgroup X (ZMod 2) i j hij) :=
  exhaustsSubgroup_of_monotone_iSup
    (elementaryRootSubgroup i j hij)
    (rootDegreeSubgroup X (ZMod 2) i j hij)
    (rootDegreeSubgroup_mono X (ZMod 2) i j hij)
    (iSup_rootDegreeSubgroup X (ZMod 2) i j hij)

/-- The internally straightened value on a free elementary root. -/
noncomputable def rootStraightenedCocycle
    (i j : Fin 3) (hij : i ≠ j)
    (rho : G X →* (E ≃ₗᵢ[ℂ] E)) (b : G X → E) (D : ℝ)
    (hb : IsQuasiCocycle rho b D) (a : G X) : E :=
  straightenedCocycle rho b D hb
    (rootDegreeSubgroup X (ZMod 2) i j hij)
    (fun n ↦ finite_rootDegreeSubgroup X (ZMod 2) i j hij n) a

/-- Straightening changes a quasi-cocycle value on the root by at most its
defect (in fact the estimate holds for every ambient element). -/
theorem norm_rootStraightenedCocycle_sub_le
    (i j : Fin 3) (hij : i ≠ j)
    {rho : G X →* (E ≃ₗᵢ[ℂ] E)} {b : G X → E} {D : ℝ}
    (hb : IsQuasiCocycle rho b D) (a : G X) :
    ‖rootStraightenedCocycle X i j hij rho b D hb a - b a‖ ≤ D :=
  norm_straightenedCocycle_sub_le hb
    (rootDegreeSubgroup X (ZMod 2) i j hij)
    (fun n ↦ finite_rootDegreeSubgroup X (ZMod 2) i j hij n) a

/-- On the full elementary root, the straightened map satisfies the exact
one-cocycle identity. -/
theorem rootStraightenedCocycle_mul
    (i j : Fin 3) (hij : i ≠ j)
    {rho : G X →* (E ≃ₗᵢ[ℂ] E)} {b : G X → E} {D : ℝ}
    (hb : IsQuasiCocycle rho b D)
    (a c : elementaryRootSubgroup i j hij) :
    rootStraightenedCocycle X i j hij rho b D hb (a * c).1 =
      rootStraightenedCocycle X i j hij rho b D hb a.1 +
        rho a.1
          (rootStraightenedCocycle X i j hij rho b D hb c.1) := by
  exact straightenedCocycle_mul_of_exhausts hb
    (elementaryRootSubgroup i j hij)
    (rootDegreeSubgroup X (ZMod 2) i j hij)
    (fun n ↦ finite_rootDegreeSubgroup X (ZMod 2) i j hij n)
    (exhausts_rootDegreeSubgroup X i j hij)
    a.1 c.1 a.property

end
end FreeRootStraightening
end GroupApproximation
