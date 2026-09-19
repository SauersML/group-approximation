import GroupApproximation.Steinberg.GeneralRankFiniteFieldPropertyT
import GroupApproximation.Leavitt.RankTwelveCorner
import GroupApproximation.Meta.AxiomGuard

/-!
# The two printed Ershov--Jaikin-Zapirain uses, as instances of the theorem

`non_mf_groups_exist.tex` invokes the Ershov--Jaikin-Zapirain theorem twice
inside its own mathematics, at exactly two ranks over exactly one ring:

* Section *The binary Leavitt self-compression*, introducing
  `H = EL₁₂(R)` and `L = EL₃(R) ≤ H`:
  "Both groups have property~(T) by the theorem of Ershov and
  Jaikin-Zapirain [EJZ, Theorem 1.1]."
* Proof of `thm:headline`:
  "The ring `R` is finitely generated, and `H` has property~(T) by the
  Ershov--Jaikin-Zapirain theorem for elementary groups over finitely
  generated rings [EJZ, Theorem 1.1]."

Both conclusions were already theorems here, but by a **different route** than
the printed one.  `BinaryLeavittSteinberg.elementaryBase_hasKazhdanPropertyT`
collapses every elementary rank over a binary Leavitt ring to rank three
through the complete left-comb prefix code of `Leavitt.LeavittRankEquivalence`,
and then spends the rank-three finite-field theorem
`finiteFieldElementaryThree_hasKazhdanPropertyT`.  That is a Leavitt-specific
argument: it uses that `R` carries a Leavitt family of index two, which the
printed sentence does not.

`Steinberg.GeneralRankFiniteFieldPropertyT` now proves the general-rank
statement outright, as the named proposition
`GeneralRankFiniteFieldElementaryPropertyT`: property `(T)` for `EL_n(A)`, for
every `n ≥ 3`, over every finite-type algebra `A` over every finite field.
This module spends that proposition at the two ranks the manuscript spends it
at, so that the Lean route matches the printed route:

* `hasKazhdanPropertyT_viaEJZ` -- the theorem at `n = 12`;
* `corner_hasKazhdanPropertyT_viaEJZ` -- the theorem at `n = 3`, transported
  along `cornerEquiv`;
* `printedBothGroupsHaveKazhdanPropertyT` -- the printed sentence
  "Both groups have property (T)", as one proposition.

The two hypotheses the printed sentence needs of `R` are discharged by
instances already in the tree, not by new work: `R = L_{𝔽₂}(1,2)` is a
`ZMod 2`-algebra because it is a `RingQuot` of `FreeAlgebra (ZMod 2)`, and it
is of finite type over `ZMod 2` by
`UniversalLeavittOver`'s `Algebra.FiniteType.of_surjective (quotientMap k)`
instance -- which is exactly the printed clause "the ring `R` is finitely
generated".

## Relation to the bespoke declarations

Nothing here replaces `RankTwelveEndpoint.hasKazhdanPropertyT` or
`RankTwelveConfiguration`'s `corner_hasKazhdanPropertyT`.  Those are used
throughout the rank-twelve development and remain the shorter proofs; they
also reach ranks `1` and `2`, which the EJZ theorem does not.  The pair of
`_eq` lemmas below records that the new declarations prove the *same*
propositions -- which they do by proof irrelevance, both being proofs of a
`Prop`; the content of the pairing is that the two statements are the same
statement, not that the two arguments are the same argument.

## Trust surface

`generalRankFiniteFieldElementaryPropertyT` is itself proved in this
repository (see its module docstring for the coefficient-ring axis it does
*not* reach, namely characteristic zero and non-prime positive
characteristic), and is audited closed in
`Endpoint/OneSidedTransportAudit`.  So routing the printed sentences through
it introduces no literature dependence: the citation in the manuscript stays
an attribution of priority.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankTwelveEndpoint

/-! ## The coefficient ring as an EJZ input -/

/-- **The printed hypothesis on the coefficient ring.**  "The ring `R` is
finitely generated": `R = L_{𝔽₂}(1,2)` is a finite-type algebra over the
finite field `𝔽₂ = ZMod 2`, which is what the Ershov--Jaikin-Zapirain theorem
asks of its coefficients.  Both halves are instances already present in the
tree; this lemma only names them at `R`. -/
theorem coefficientRing_finiteType : Algebra.FiniteType (ZMod 2) R :=
  inferInstance

/-! ## The theorem at the two printed ranks -/

/-- **"`H` has property (T) by the Ershov--Jaikin-Zapirain theorem for
elementary groups over finitely generated rings."**  (`non_mf_groups_exist.tex`,
proof of `thm:headline`.)

This is `generalRankFiniteFieldElementaryPropertyT` applied at the finite field
`k = ZMod 2`, the finite-type algebra `A = R = L_{𝔽₂}(1,2)`, and the rank
`n = 12`.  It is the printed derivation, not a Leavitt-specific one: nothing
about the index-two Leavitt family of `R` is used, only that `R` is a finitely
generated `𝔽₂`-algebra. -/
theorem hasKazhdanPropertyT_viaEJZ : HasKazhdanPropertyT.{0, 0} H :=
  generalRankFiniteFieldElementaryPropertyT (ZMod 2) R 12 (by norm_num)

/-- **The corner half of "Both groups have property (T) by the theorem of
Ershov and Jaikin-Zapirain."**  (`non_mf_groups_exist.tex`, section *The binary
Leavitt self-compression*.)

`generalRankFiniteFieldElementaryPropertyT` applied at `k = ZMod 2`, `A = R`
and the rank `n = 3` gives property `(T)` for `EL₃(R)`.  The printed `L` is the
upper-left corner subgroup of `H`, and `RankTwelve.cornerEquiv` identifies it
with `EL₃(R)` -- an isomorphism, so the transport needs no surjectivity
argument. -/
theorem corner_hasKazhdanPropertyT_viaEJZ : HasKazhdanPropertyT.{0, 0} corner :=
  HasKazhdanPropertyT.of_mulEquiv cornerEquiv.symm
    (generalRankFiniteFieldElementaryPropertyT (ZMod 2) R 3 (by norm_num))

/-- **The printed sentence, whole.**  "Both groups have property~(T) by the
theorem of Ershov and Jaikin-Zapirain [EJZ, Theorem 1.1]" -- `H = EL₁₂(R)` and
the upper-left corner `L = EL₃(R)`, each an instance of the formalized
Ershov--Jaikin-Zapirain theorem at its own rank. -/
theorem printedBothGroupsHaveKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} H ∧ HasKazhdanPropertyT.{0, 0} corner :=
  ⟨hasKazhdanPropertyT_viaEJZ, corner_hasKazhdanPropertyT_viaEJZ⟩

/-! ## Agreement with the bespoke route

Both members of each pair are proofs of the same `Prop`, so they are equal by
proof irrelevance.  What the two lemmas record is that the EJZ instance proves
*the statement the rank-twelve development already uses*, with no change of
group, rank, or universe -- so either proof may be substituted for the other
at every call site. -/

theorem hasKazhdanPropertyT_viaEJZ_eq_bespoke :
    hasKazhdanPropertyT_viaEJZ = hasKazhdanPropertyT :=
  rfl

theorem corner_hasKazhdanPropertyT_viaEJZ_eq_bespoke :
    corner_hasKazhdanPropertyT_viaEJZ = corner_hasKazhdanPropertyT :=
  rfl

end RankTwelveEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation
open GroupApproximation.Manuscript.OneSidedMFRadical

#audit_closed_axioms RankTwelveEndpoint.hasKazhdanPropertyT_viaEJZ
#audit_closed_axioms RankTwelveEndpoint.corner_hasKazhdanPropertyT_viaEJZ
#audit_closed_axioms RankTwelveEndpoint.printedBothGroupsHaveKazhdanPropertyT
