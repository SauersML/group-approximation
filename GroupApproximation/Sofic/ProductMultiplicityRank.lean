import GroupApproximation.Algebra.TorsionFreeRank
import GroupApproximation.Sofic.ProductMultiplicity

/-!
# Infinite multiplicity, separated by torsion-free rank

The manuscript's multiplicity paragraph (`non_mf_groups_exist.tex`; navigate by the
sentence, the line numbers drift) reads:

> The groups `E × ℤ^k` for `k ≥ 0` are finitely presented, pairwise
> nonisomorphic, and non-MF, each containing `E`.  They are pairwise
> nonisomorphic because their abelianizations have distinct torsion-free
> ranks; the number of homomorphisms to `ℤ/2` separates them as well.

The badge on that paragraph sits on
`ProductMultiplicity.manuscriptInfiniteMultiplicity`, which now states both
of the invariants the manuscript names — the torsion-free rank first, the
`ℤ/2` count second — and so needs the rank specialization for the chosen
witness in that file.  This file is the general development the specialization
is an instance of: it runs the printed argument for an arbitrary finitely
generated first factor, through `Algebra.TorsionFreeRank`:

* `(E × ℤ^k)^{ab} ≅ E^{ab} × ℤ^k`, because abelianization commutes with
  binary products;
* the torsion-free rank is additive over products, and `ℤ^k` contributes
  exactly `k`, so the rank of `(E × ℤ^k)^{ab}` is `rk E^{ab} + k`;
* `E` is finitely presented, hence finitely generated, hence `rk E^{ab}`
  is *finite* --- which is what makes `rk E^{ab} + k` determine `k`;
* isomorphic groups have equal invariants, so distinct `k` give
  nonisomorphic groups.

The finite presentation and the failure of MF are unchanged from
`Sofic.ProductMultiplicity` and are reused from there; only the
separation argument is redone.  The counting proof stays in place as an
independent second route to the same conclusion.

The rank lemmas below are stated for a general first factor and are the ones
to reuse.  Their short `MarkedGroup`-only counterparts live in
`Sofic.ProductMultiplicity` under different names
(`torsionFreeRank_intPow`, `torsionFreeRank_family`,
`chosenFamily_torsionFreeRank_ne`) because that file is imported by this one
and the badge declaration is there; the duplication is one short induction
and is deliberate, since reversing the import would move the badged
declaration out of the module the manuscript cites.
-/

namespace GroupApproximation
namespace ProductMultiplicityRank

open ProductMultiplicity
open TorsionFreeRank

/-! ## The rank of the free abelian factor -/
/-! ## The rank of a family member -/

/-- **The manuscript's invariant of `G × ℤ^k`.**  Its abelianization has
torsion-free rank `rk G^{ab} + k`. -/
theorem abelianizationRank_family (G : Type) [Group G] (k : ℕ) :
    abelianizationRank (Family G k) = abelianizationRank G + (k : Cardinal) := by
  calc abelianizationRank (Family G k)
      = abelianizationRank G + abelianizationRank (IntPow k) :=
        abelianizationRank_prod G (IntPow k)
    _ = abelianizationRank G + (k : Cardinal) := by rw [GroupApproximation.ProductMultiplicity.torsionFreeRank_intPow]

/-- **The invariant determines `k`.**  Finite generation of `G` makes
`rk G^{ab}` a natural number, and cancellation in `ℕ` finishes.  This is
the step that fails for an infinite rank, which is why finite
presentation of `E` is used and not just its existence. -/
theorem eq_of_abelianizationRank_family_eq {G : Type} [Group G] [Group.FG G] {k l : ℕ}
    (h : abelianizationRank (Family G k) = abelianizationRank (Family G l)) : k = l := by
  rw [abelianizationRank_family, abelianizationRank_family] at h
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp (abelianizationRank_lt_aleph0 G)
  rw [hn, ← Nat.cast_add, ← Nat.cast_add] at h
  exact Nat.add_left_cancel (Nat.cast_injective h)

/-- **Distinct `k` give distinct torsion-free ranks.**  This is the
manuscript's parenthetical, stated positively. -/
theorem abelianizationRank_family_ne {G : Type} [Group G] [Group.FG G] {k l : ℕ}
    (h : k ≠ l) :
    abelianizationRank (Family G k) ≠ abelianizationRank (Family G l) :=
  fun hEq => h (eq_of_abelianizationRank_family_eq hEq)

/-- **The members of the family are pairwise nonisomorphic**, because an
isomorphism would equate their abelianizations' torsion-free ranks. -/
theorem eq_of_family_mulEquiv_rank {G : Type} [Group G] [Group.FG G] {k l : ℕ}
    (e : Family G k ≃* Family G l) : k = l :=
  eq_of_abelianizationRank_family_eq (abelianizationRank_congr e)

/-! ## The chosen witness -/

open ChosenMarkedPresentation

/-- The abelianization of `E × ℤ^k` has torsion-free rank `rk E^{ab} + k`. -/
theorem chosenFamily_abelianizationRank (k : ℕ) :
    abelianizationRank (Family MarkedGroup k)
      = abelianizationRank MarkedGroup + (k : Cardinal) :=
  abelianizationRank_family MarkedGroup k

/-- `E^{ab}` has finite torsion-free rank, `E` being finitely presented. -/
theorem chosenAbelianizationRank_lt_aleph0 :
    abelianizationRank MarkedGroup < Cardinal.aleph0 := by
  haveI : Group.FG MarkedGroup :=
    ProductFinitePresentation.fg_of_isFinitelyPresented MarkedGroup
  exact abelianizationRank_lt_aleph0 MarkedGroup
/-- **The manuscript's multiplicity paragraph, with its own invariant.**
There is an infinite family of finitely presented groups, none of them
operator-MF, whose abelianizations have pairwise distinct torsion-free
ranks --- and which are therefore pairwise nonisomorphic. -/
theorem manuscriptInfiniteMultiplicityRank :
    ∃ F : ℕ → Type,
      ∃ _ : ∀ k, Group (F k),
        (∀ k, Group.IsFinitelyPresented (F k)) ∧
          (∀ k, ¬ IsOperatorMF (F k)) ∧
            (∀ k l, k ≠ l → abelianizationRank (F k) ≠ abelianizationRank (F l)) ∧
              (∀ k l, Nonempty (F k ≃* F l) → k = l) := by
  refine ⟨fun k ↦ Family MarkedGroup k, fun _ ↦ inferInstance,
    fun k ↦ (chosenFamily_finitelyPresented_not_isOperatorMF k).1,
    fun k ↦ (chosenFamily_finitelyPresented_not_isOperatorMF k).2,
    fun k l h ↦ GroupApproximation.ProductMultiplicity.chosenFamily_torsionFreeRank_ne h, ?_⟩
  rintro k l ⟨e⟩
  exact GroupApproximation.ProductMultiplicity.chosenFamily_eq_of_mulEquiv e

end ProductMultiplicityRank
end GroupApproximation
