import GroupApproximation.GGT.HullSCRelatorSeparation2Diagonal
import GroupApproximation.GGT.OsinTheorem54SepElementaryBall

/-!
# The diagonal leaf, discharged

`GGT/HullSCRelatorSeparation2Diagonal.lean` carries its clause as a named
hypothesis: no nontrivial element of the relative `eps`-ball commutes with a
positive power of the loxodromic.  I recorded it as a leaf and asked whether a
core could be chosen to satisfy it.  The answer, in
`GGT/OsinTheorem54SepElementaryBall.lean`, is that nothing has to be chosen: in
a torsion-free group it holds for **every** loxodromic, because the relative
ball lies in the family, the family meets the elementary closure of a loxodromic
only in torsion, and there is none.

The step from commuting to the elementary closure is the definition:
`Elementary.elementaryClosure g` collects the `h` with `h g^n h⁻¹ = g^m` for
some nonzero `n`, `m`, and an element commuting with `g^d` supplies `n = m = d`.

`noCommute_of_torsionFree` is the discharge, in exactly the shape
`HullSC.exists_separated_relator_exponents₂_diagonal` asks for.  Torsion-freeness
is the manuscript's hypothesis about the groups it studies, not a leaf: the whole
programme is about torsion-free groups.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.GGT

universe u

section NoCommute

variable {G : Type u} [Group G]

/-- **An element commuting with a power lies in the elementary closure.** -/
theorem mem_elementaryClosure_of_commute {g x : G} {d : ℕ} (hd : 0 < d)
    (hcomm : Commute x (g ^ d)) : x ∈ Elementary.elementaryClosure g := by
  show ∃ n m : ℤ, n ≠ 0 ∧ m ≠ 0 ∧ x * g ^ n * x⁻¹ = g ^ m
  refine ⟨(d : ℤ), (d : ℤ), by omega, by omega, ?_⟩
  exact_mod_cast (show x * g ^ d * x⁻¹ = g ^ d by rw [hcomm.eq, mul_inv_cancel_right])

/-- **The diagonal clause holds of every loxodromic, in a torsion-free group.**

No choice of core is needed; this is the hypothesis
`HullSC.exists_separated_relator_exponents₂_diagonal` takes, discharged. -/
theorem noCommute_of_torsionFree {D : GGT.RelGenSet G Bool}
    (hacy : IsAcylindrical G (Cayley D.alphabet)) {a : Bool → G}
    (hlox : ∀ s : Bool, IsLoxodromic (a s) (Cayley.base D.alphabet))
    (htf : ∀ y : G, IsOfFinOrder y → y = 1) (eps : ℕ) :
    ∀ s : Bool, ∀ x ∈ D.relBall s eps, x ≠ 1 → ∀ d : ℕ, 0 < d →
      ¬ Commute x (a s ^ d) := by
  intro s x hx hx1 d hd hcomm
  refine hx1 ?_
  exact GGT.OsinComponents.eq_one_of_mem_relBall_of_mem_elementaryClosure D s
    hacy (hlox s) htf hx (mem_elementaryClosure_of_commute hd hcomm)

end NoCommute

end HullSC
end GroupApproximation
