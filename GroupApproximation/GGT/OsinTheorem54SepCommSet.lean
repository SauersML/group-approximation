import GroupApproximation.GGT.OsinTheorem54SepCommIndex

/-!
# `sep_comm`, assembled

The `sep_comm` field of `GGT.OsinEnlargement.SepData` and `SepDataFam`, for the
concrete count, and as a **set equality** rather than a comparison of
cardinalities: on a symmetric base `S(f,g;D)` and `S(g,f;D)` have the same
members.

Three landed facts assemble it, one per thing reversal does to a witness:

* `isGeodesicWord_revWord` --- the reversed word is a geodesic the other way;
* `isComp_revWord` --- its component sits at the reversed indices
  `[|w| - k, |w| - i)`;
* `mk_vertex_revWord_eq` --- and records the *same coset*, the reversed path
  naming it at the far endpoint of the original run, which differs from the near
  one by the run's span and so lies in the same coset.

The only arithmetic is that essential penetration survives: the reversed span is
the inverse of the original, and `relBall_inv` says `d̂_λ` does not see the
difference.

The symmetry of the base is threaded as a hypothesis and is not a restriction:
`exists_symmetric_base'` supplies it for free, and without it the field is
outright false --- `GGT/OsinTheorem54SepCommRefuted.lean` refutes it at
`X = {t}`, `H = G`.

Unconditional: neither `LemmaFourEight` nor `IsolatedComponentBound` is used.
In particular this does not need `sepSet` to be finite --- it is an equality of
sets, and `sepCard_comm` follows whether or not they are.

## The degenerate family, and why it is harmless

Recorded here because it is the first thing a reader checks and the answer is
not the obvious one.  Take `Λ = Unit`, `G = ℤ`, `H = ⊥` and `X = {t, t⁻¹}`.
This is hyperbolically embedded: the Cayley graph is a line, and the relative
ball lies in `⊥`.  A component is a maximal run of `comp () h` with `h ∈ ⊥`, so
`h = 1`; but a geodesic word cannot contain a letter of value `1`, since
deleting it gives a strictly shorter legal expression of the same element.  So
geodesics carry no components at all, `sepSet` is empty, `sepCard` is `0`, and
Osin's `Y = {y | S(1,y;D) = ∅}` is the **whole of `G`** --- the enlargement
swallows the group and `Γ(G, Y ⊔ ℋ)` is complete.

That looks like it should refute `AcylindricalCore`, since on a complete graph
every stabiliser set is all of `G` and hence infinite.  It does not.
`AcylindricalCore` quantifies over `z` at distance *exactly* `R` and need only
produce *some* `R > 0`, so `R = 2` makes its inner condition vacuous, the graph
having diameter one; and `IsAcylindrical` is vacuous on a bounded space for the
same reason.  So every field holds here, and the degenerate family is not a
counterexample to Theorem 5.4 but a case where the conclusion is vacuous.

This is exactly why `GGT/OsinSeparatingCosets.lean` states the core with `= R`
rather than `≥ R`: the `≥ R` form would not merely be stronger than Osin proves,
it would be **false** at this model.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **`S(f,g;D)` and `S(g,f;D)` are the same set**, on a symmetric base. -/
theorem sepSet_comm (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (f g : G) :
    sepSet D lam Dc f g = sepSet D lam Dc g f := by
  have key : ∀ a b : G, sepSet D lam Dc a b ⊆ sepSet D lam Dc b a := by
    intro a b c hc
    obtain ⟨w, i, k, hgw, hpen, rfl⟩ := hc
    have hb : a * RelLetter.listVal w = b := hgw.2.1
    subst hb
    refine ⟨revWord w, w.length - k, w.length - i,
      isGeodesicWord_revWord D hsymm hgw,
      ⟨isComp_revWord lam w hpen.1, ?_⟩, ?_⟩
    · rw [vertex_revWord_of_end w a k, vertex_revWord_of_end w a i]
      intro hmem
      refine hpen.2 ?_
      have hinv := relBall_inv D lam hsymm hmem
      rwa [mul_inv_rev, inv_inv] at hinv
    · exact (mk_vertex_revWord_eq D lam a hgw.1 hpen.1).symm
  exact Set.Subset.antisymm (key f g) (key g f)

/-- **`sep_comm`, for the concrete count.**  A corollary of the set equality, so
it holds whether or not the sets are finite. -/
theorem sepCard_comm (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (f g : G) :
    sepCard D lam Dc f g = sepCard D lam Dc g f := by
  show (sepSet D lam Dc f g).ncard = (sepSet D lam Dc g f).ncard
  rw [sepSet_comm D lam Dc hsymm f g]

end OsinComponents
end GGT
end GroupApproximation
