import GroupApproximation.CharClass.CohomologyContractible
import GroupApproximation.CharClass.CohomologyLHDegreewise

/-!
# Over a contractible base, only the top Leray–Hirsch coordinate survives

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

This is the reason the Thom class is nonzero locally, isolated so that nobody has
to rediscover it inside a naturality argument.

At the top degree `2r` the `i`-th Leray–Hirsch coefficient lies in `H^{2r-2i}` of
the base.  For `i < r` that degree is at least two, so over a **contractible**
base every such coefficient is already zero and the whole column vanishes.  Only
the coefficient at `i = r` survives, and it lives in `H^0`, where the unit class
is nonzero as soon as the base is nonempty.

So restricting a Leray–Hirsch presentation to a contractible neighbourhood kills
every coordinate but the top one, and the top one is what the Thom class was
built to make equal to the unit.

**What this does not do**, since I said otherwise to another lane before catching
it.  The statement is about column terms, so it needs no Leray–Hirsch instance
over the neighbourhood *to hold*.  But applying it to a restricted class requires
knowing that class **is** a combination of column terms, and that is surjectivity
of the combination downstairs, which is exactly a presentation over the
neighbourhood.  So this removes the final computation and not the instance.  A
correct statement travelling with an overstated account of what it buys is the
failure this lane has now met three times, and no probe sees it.

## Main declarations

* `LH.lhTerm_eq_zero_of_contractible` — the lower columns vanish.
* `LH.sum_lhTerm_eq_top_of_contractible` — **only the top column survives.**
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace LH

variable {Y : Type} [TopologicalSpace Y] [ContractibleSpace Y] {P : TopCat.{0}}

/-- **Below the top index, the column vanishes over a contractible base.**  Its
coefficient lies in a positive degree, where there is nothing. -/
theorem lhTerm_eq_zero_of_contractible (π : P ⟶ TopCat.of Y) (ξ : Hmod2 P 2)
    {r i : ℕ} (hi : i < r) (a : Hmod2 (TopCat.of Y) (2 * r - 2 * i)) :
    lhTerm π ξ (2 * r) i a = 0 := by
  have ha : a = 0 :=
    cohomology_eq_zero_of_contractible Y (2 * r - 2 * i) (by omega) a
  rw [ha, lhTerm_zero]

/-- **Only the top column survives over a contractible base.** -/
theorem sum_lhTerm_eq_top_of_contractible (π : P ⟶ TopCat.of Y) (ξ : Hmod2 P 2)
    (r : ℕ) (a : (i : Fin (r + 1)) → Hmod2 (TopCat.of Y) (2 * r - 2 * (i : ℕ))) :
    ∑ i : Fin (r + 1), lhTerm π ξ (2 * r) (i : ℕ) (a i)
      = lhTerm π ξ (2 * r) r (a (Fin.last r)) := by
  rw [Fin.sum_univ_castSucc]
  have hzero : ∑ i : Fin r, lhTerm π ξ (2 * r) ((i.castSucc : Fin (r + 1)) : ℕ)
      (a i.castSucc) = 0 :=
    Finset.sum_eq_zero fun i _ =>
      lhTerm_eq_zero_of_contractible π ξ
        (by rw [Fin.val_castSucc]; exact i.isLt) (a i.castSucc)
  rw [hzero, zero_add]
  rfl

/-! Printed on every build. -/

#print axioms sum_lhTerm_eq_top_of_contractible

end LH

end

end GroupApproximation.CharClass
