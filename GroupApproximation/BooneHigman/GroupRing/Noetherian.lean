import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Group rings of finitely generated commutative groups are Noetherian

This is P. Hall's starting point for finitely generated metabelian groups. If `Q` is a finitely
generated commutative group, then the group ring `ℤ[Q]` is a Noetherian ring. So every finitely
generated `ℤ[Q]`-module is a Noetherian module, and every submodule of one is finitely generated.

The proof is Hilbert's basis theorem in Mathlib's form:
- `R[Q]` is a finitely generated `R`-algebra (`MonoidAlgebra.finiteType_of_fg`);
- a finitely generated algebra over a Noetherian ring is Noetherian
  (`Algebra.FiniteType.isNoetherianRing`).

* `isNoetherianRing_monoidAlgebra`: `R[Q]` is Noetherian when `R` is Noetherian and `Q` is a finitely
  generated commutative monoid.
* `isNoetherianRing_intGroupRing`: the case `R = ℤ` for a finitely generated commutative group.
* `isNoetherian_of_finite`: finitely generated `R[Q]`-modules are Noetherian.
* `submodule_fg_of_finite`: their submodules are finitely generated.
-/

namespace GroupApproximation
namespace BooneHigman
namespace GroupRing

section General

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {Q : Type*} [CommMonoid Q] [Monoid.FG Q]

/-- **Hilbert's basis theorem for monoid rings.** The monoid ring of a finitely generated
commutative monoid over a Noetherian ring is Noetherian. -/
instance isNoetherianRing_monoidAlgebra : IsNoetherianRing (MonoidAlgebra R Q) :=
  Algebra.FiniteType.isNoetherianRing R (MonoidAlgebra R Q)

/-- Finitely generated modules over `R[Q]` are Noetherian modules. -/
theorem isNoetherian_of_finite (M : Type*) [AddCommGroup M] [Module (MonoidAlgebra R Q) M]
    [Module.Finite (MonoidAlgebra R Q) M] : IsNoetherian (MonoidAlgebra R Q) M :=
  inferInstance

/-- Every submodule of a finitely generated `R[Q]`-module is finitely generated. -/
theorem submodule_fg_of_finite {M : Type*} [AddCommGroup M] [Module (MonoidAlgebra R Q) M]
    [Module.Finite (MonoidAlgebra R Q) M] (N : Submodule (MonoidAlgebra R Q) M) : N.FG :=
  IsNoetherian.noetherian N

end General

/-- The integral group ring of a finitely generated commutative group is Noetherian. -/
theorem isNoetherianRing_intGroupRing (Q : Type*) [CommGroup Q] [Group.FG Q] :
    IsNoetherianRing (MonoidAlgebra ℤ Q) :=
  inferInstance

end GroupRing
end BooneHigman
end GroupApproximation
