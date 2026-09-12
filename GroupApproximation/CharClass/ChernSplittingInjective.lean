import GroupApproximation.CharClass.ChernWhitneyFlag

/-!
# The splitting data from injectivity alone

`splittingDataOfGraded` asks for a Leray–Hirsch structure and uses it in exactly one
place, to get injectivity of the pullback on the ring.  That is an over-ask, and
`cc-wu` found that it is a fatal one for the case the splitting principle is for: the
flag projection is an *iterated* projectivisation, so there is no Leray–Hirsch
structure for it on a single class, at any rank.  One projectivisation splits off one
root; the tower is a composite.

So this file states the same builders taking injectivity directly.  Nothing else
changes, and the earlier names keep standing under rule 11.  A consumer holding a
Leray–Hirsch structure still supplies the hypothesis in one line, so this is the
general form rather than a special case.

The pattern is worth naming, because it is the third time in this lane: **ask for
the property you consume, not the structure that would imply it.**  The tell is that
the hypothesis occurs exactly once in the file.

## Main declarations

* `splittingDataOfInjective` — `cc-wu`'s splitting data, from injectivity.
* `hasSplitting_of_injective` — the same with the flag space hidden.
* `hasSplitting_of_splitPoly_injective` — and with the polynomial splitting supplied.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory Polynomial

noncomputable section

/-- **`cc-wu`'s splitting data, from injectivity of the pullback.**  The Leray–Hirsch
structure was never used for anything else. -/
def splittingDataOfInjective {N F : TopCat.{0}} {r : ℕ} {γ : ℕ → TotalH N}
    (proj : F ⟶ N) (hinj : Function.Injective (TotalH.map proj))
    (root : ℕ → Hmod2 F 2)
    (hroot : ∀ l : ℕ, ∃ (d : ℕ) (g : F ⟶ CPtop d) (h : Hmod2 (CPtop d) 2),
      root l = pull g 2 h)
    (hsplit : ∀ k : ℕ, TotalH.map proj (γ k)
      = esymmOn (Finset.range r) (fun l => TotalH.of F 2 (root l)) k) :
    Wu.SplittingData N F r γ where
  proj := proj
  root := root
  pull_injective := hinj
  sq_one_root := fun l => by
    obtain ⟨d, g, h, hg⟩ := hroot l
    rw [hg]
    exact CPn.sq_one_pull_eq_zero g h
  chern_split := hsplit

/-- The same with the flag space and the rank hidden. -/
theorem hasSplitting_of_injective {N F : TopCat.{0}} {r : ℕ} {γ : ℕ → TotalH N}
    (proj : F ⟶ N) (hinj : Function.Injective (TotalH.map proj))
    (root : ℕ → Hmod2 F 2)
    (hroot : ∀ l : ℕ, ∃ (d : ℕ) (g : F ⟶ CPtop d) (h : Hmod2 (CPtop d) 2),
      root l = pull g 2 h)
    (hsplit : ∀ k : ℕ, TotalH.map proj (γ k)
      = esymmOn (Finset.range r) (fun l => TotalH.of F 2 (root l)) k) :
    Wu.HasSplitting N γ :=
  ⟨F, r, ⟨splittingDataOfInjective proj hinj root hroot hsplit⟩⟩

/-- **The splitting principle from injectivity and the split relation.**  Whitney is
`chern_split_of_splitPoly`; this is the form the flag bundle can actually supply,
since it never mentions a Leray–Hirsch structure for the tower. -/
theorem hasSplitting_of_splitPoly_injective {N F P : TopCat.{0}}
    (D : LerayHirschData N P) (proj : F ⟶ N)
    (hinj : Function.Injective (TotalH.map proj))
    (r : ℕ) (hr : D.rank = r) (root : ℕ → Hmod2 F 2)
    (hroot : ∀ l : ℕ, ∃ (d : ℕ) (g : F ⟶ CPtop d) (h : Hmod2 (CPtop d) 2),
      root l = pull g 2 h)
    (hsplit : D.chernPolynomial.map (TotalH.map proj)
      = ∏ l ∈ Finset.range r, (X + C (TotalH.of F 2 (root l)))) :
    Wu.HasSplitting N D.chern :=
  hasSplitting_of_injective proj hinj root hroot
    (chern_split_of_splitPoly D proj r hr root hsplit)

end

end LH
end CharClass
end GroupApproximation
