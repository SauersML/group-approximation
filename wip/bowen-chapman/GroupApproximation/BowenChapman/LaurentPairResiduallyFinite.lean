import GroupApproximation.BowenChapman.LaurentPair
import GroupApproximation.BowenChapman.ResiduallyFiniteSubstitution

/-!
# The ambient group is residually finite

`ambient_residuallyFinite` shows that `Ambient = EL₃(𝔽₂[ℤ³]) ⋊ EL₃(ℤ)` from
`GroupApproximation.BowenChapman.LaurentPair` is residually finite.  The actor substitutes
exponents entrywise, so this is the case `k = 𝔽₂`, `ι = Fin 3` of
`CongruenceQuotient.residuallyFinite_semidirectProduct_of_expSubst`, whose finite quotients
reduce exponents modulo `n`.
-/

namespace GroupApproximation.BowenChapman

open CongruenceQuotient

/-- Monomial substitution by an element of the actor is `expSubst` of its integer matrix. -/
theorem substitution_apply_eq_expSubst (M : Actor) (a : Laurent) :
    substitution M a =
      expSubst (ZMod 2) ((M : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) : Matrix (Fin 3) (Fin 3) ℤ) a := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single v c => rw [substitution_single, expSubst_single]

/-- **The ambient group `EL₃(𝔽₂[ℤ³]) ⋊ EL₃(ℤ)` is residually finite.** -/
theorem ambient_residuallyFinite : Group.ResiduallyFinite Ambient :=
  residuallyFinite_semidirectProduct_of_expSubst actorAction fun M B i j => by
    rw [actorAction_coe_apply, substitution_apply_eq_expSubst]

end GroupApproximation.BowenChapman
