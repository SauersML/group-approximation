import GroupApproximation.CharClass.CartanMasterEval

/-!
# The Cartan formula, at cochain level

Both composites are now evaluated, so the master identity reads as an identity
between cochains: the square of the cup product, the sum of the cup products of
the two squares, and a coboundary.

Every degree is carried as a parameter with its defining equation, which is what
keeps the statement free of transports. Exactly one cast survives, on the square
of the cup product, and it is unavoidable: `sqCochain` fixes its own output
degree as a sum, while the coboundary fixes the simplex degree as a successor,
and those two spellings of one number cannot both be definitional. That cast is
the one `cocycleClass_cast` undoes when the identity passes to classes.

## Main results

* `fourEval_compA_single'` — composite A evaluated, with the index free.
* `cartan_cochainEval` — **the Cartan formula, evaluated on a simplex**.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- Composite A evaluated on a basis element, with the total degree and the
source index carried as parameters. -/
theorem fourEval_compA_single' (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (k j : ℕ) (hk : p + q + (p + q) = k) (hj : j ≤ p + q)
    (i : Fin (k + 1)) (hi : j + (p + q) = i.val)
    (σ : singularSimplices X i.val) :
    fourEvalF2 X p q α β k
        (((compA.app X).f k).hom
          (Finsupp.single (⟨i, simplexEquiv X i.val σ⟩ : WSIndex k X) (1 : GroupRingZ2)))
      = cochainEval i.val
          (cochainCast hi (sqCochain (p + q) j (cochainCup p q α β))) σ := by
  subst hk
  obtain ⟨iv, ihv⟩ := i
  cases hi
  refine Eq.trans (fourEval_compA_single X p q α β j hj σ) ?_
  exact congrArg (fun γ => cochainEval (j + (p + q)) γ σ) (cochainCast_rfl _).symm

/-- **The Cartan formula at cochain level**, evaluated on a simplex.  The square
of the cup product is the sum of the cup products of the two squares, plus a
coboundary. -/
theorem cartan_cochainEval (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (hα : cochainCoboundary (ZMod 2) X p α = 0)
    (hβ : cochainCoboundary (ZMod 2) X q β = 0)
    (n j d e : ℕ) (hn : n + 1 = p + q + (p + q)) (hj : j ≤ p + q)
    (hd : d + 1 = j + (p + q)) (he : d + 1 + e = n + 1) (hdn : d < n + 1)
    (σ : singularSimplices X (d + 1)) :
    cochainEval (d + 1)
        (cochainCast hd.symm (sqCochain (p + q) j (cochainCup p q α β))) σ
      = (∑ j' ∈ Finset.range (e + 1),
          evAt X (p + p - j' + (q + q - (e - j')))
            (cochainCup (p + p - j') (q + q - (e - j'))
              (cochainCupI j' p p (p + p - j') α α)
              (cochainCupI (e - j') q q (q + q - (e - j')) β β)) (d + 1) σ)
        + cochainEval (d + 1)
            (cochainCoboundary (ZMod 2) X d
              (homCochain Steenrod.compBNat compA_eq_compBNat_zero X p q α β n
                ⟨d, hdn⟩)) σ := by
  have hmaster := cartan_master X p q α β hα hβ n ⟨d, hdn⟩ σ
  rw [fourEval_compA_single' X p q α β (n + 1) j hn.symm hj
      (Fin.succ (⟨d, hdn⟩ : Fin (n + 1))) hd.symm σ,
    compB_single_eq X (n + 1) (Fin.succ (⟨d, hdn⟩ : Fin (n + 1))) σ,
    show n + 1 - (Fin.succ (⟨d, hdn⟩ : Fin (n + 1))).val = e from by
      simp only [Fin.val_succ]
      omega,
    ] at hmaster
  exact hmaster.trans
    (congr_arg₂ (· + ·) (fourEvalF2_compBGen' p q α β (n + 1) e (d + 1) he σ) rfl)

end

end GroupApproximation.CharClass
