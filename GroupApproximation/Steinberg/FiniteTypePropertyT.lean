import GroupApproximation.Steinberg.FreePropertyT
import GroupApproximation.Steinberg.Functoriality
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.RingTheory.FiniteType

/-!
# Direct Steinberg property (T) over finite-type characteristic-two algebras

Every finite-type `ZMod 2`-algebra is a quotient of a free algebra on a
finite type.  Functoriality of the Steinberg presentation therefore descends
the direct free-algebra theorem to rank three over the quotient.  This uses
neither the canonical map to the elementary group nor any unstable `K₂`
statement.
-/

namespace GroupApproximation

noncomputable section

variable {R : Type} [Ring R] [Algebra (ZMod 2) R]
  [Algebra.FiniteType (ZMod 2) R]

/-- Rank-three Steinberg groups over finite-type `𝔽₂`-algebras have
Kazhdan's property `(T)`, directly and without a Steinberg-kernel premise. -/
theorem finiteTypeSteinbergThree_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} (SteinbergGroup (Fin 3) R) := by
  obtain ⟨X, hX, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_freeAlgebra'
      (R := ZMod 2) (A := R)).mp inferInstance
  letI : Fintype X := hX
  exact HasKazhdanPropertyT.of_surjective
    (SteinbergGroup.ringMap (I := Fin 3) f.toRingHom)
    (SteinbergGroup.ringMap_surjective_of_surjective f.toRingHom hf)
    (SteinbergFreePropertyT.freeSteinberg_hasKazhdanPropertyT X)

end
end GroupApproximation
