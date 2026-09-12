import GroupApproximation.CharClass.OddPTupleSign

/-!
# The slot boundary squares to zero, by construction

With `tagBd` defined as `singFreeR`'s differential retagged (`OddPTuple.lean`),
this is `HomologicalComplex.d_comp_d` plus the bookkeeping of extending a map on
tagged simplices linearly.  No bridge between an explicit sum and a differential
is needed, because there is no explicit sum: that route is `OddPTupleBd.lean`,
parked and red, and its docstring explains why it is not worth reviving.

This is the second of the three groups of the tuple square-zero law.  The other
two are the mixed terms, which cancel by the prefix asymmetry of
`OddPTupleSign.lean`, and they need nothing from this file beyond its statement.

## STATUS: PARKED AND RED (2026-09-10).  Imported by nothing.

Six probe rounds; two errors survive, and they are the same two that defeated the
bridge file, so they are *not* artifacts of that design and the redefinition did
not cause them.  What the redefinition **did** buy is real and is kept:
`OddPTuple.lean` and `OddPTupleSign.lean` are green with `tagBd` defined as the
retagged differential, so the degree drop and square-zero are true by
construction wherever they are needed downstream.

* `tagBdL_single` reports `typeclass instance problem is stuck` on
  `Module ?m ?m`.  I have tried it as a rewrite chain and with `one_smul` given
  as a term with the ring named; neither cleared it.  The stuck metavariable is
  therefore introduced by `Finsupp.linearCombination_single` itself, not by
  `one_smul`, and the fix is probably to pin the module in the statement of
  `tagBdL` rather than in this proof.
* the degree-`n+2` branch's rewrite still misses.  I did fix one genuine cause
  by reading the goal: the goal spells the top degree `n + 1 + 1` and my lemma
  said `n + 2`, which are equal by definition and not as terms, and the number
  sits inside the type of a `ModuleCat` object.  Correcting it was necessary and
  not sufficient.

**Method note, and it is the honest one.**  Rounds three through six were spent
fixing one visible symptom at a time without ever printing the whole goal at the
second error.  The one round where I did read the goal found a real bug
immediately.  Whoever resumes: print both goals first, in one round, before
editing anything.

**Do not** revive the explicit-sum bridge (`OddPTupleBd.lean`) or try to prove
square-zero from the simplicial identity; that identity is absent from the
vendored layer, and both alternatives are strictly larger than what is left here.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

variable (K : Type) [CommRing K] (X : TopCat.{0})

/-- The boundary of a tagged simplex, extended linearly. -/
def tagBdL : (TagSimp X →₀ K) →ₗ[K] (TagSimp X →₀ K) :=
  Finsupp.linearCombination K (tagBd K X)

@[simp] theorem tagBdL_single (τ : TagSimp X) :
    tagBdL K X (Finsupp.single τ (1 : K)) = tagBd K X τ := by
  rw [tagBdL, Finsupp.linearCombination_single]
  -- `one_smul` as a rewrite leaves the module a metavariable and the instance
  -- search reports `Module ?m ?m`; as a term with the ring named it is decided.
  exact one_smul K (tagBd K X τ)

/-- Differentiating a chain tagged at one degree is differentiating each of its
simplices as a tag.  Both sides are linear, so it is checked on singletons. -/
theorem tagBdL_tagAt (n : ℕ) (z : singularSimplices X n →₀ K) :
    tagBdL K X (tagAt K X n z)
      = Finsupp.linearCombination K (fun σ' => tagBd K X (⟨n, σ'⟩ : TagSimp X)) z := by
  refine LinearMap.congr_fun ?_ z
  apply Finsupp.lhom_ext'
  intro σ
  apply LinearMap.ext_ring
  show tagBdL K X (tagAt K X n (Finsupp.single σ (1 : K)))
    = Finsupp.linearCombination K (fun σ' => tagBd K X (⟨n, σ'⟩ : TagSimp X))
        (Finsupp.single σ (1 : K))
  rw [tagAt_single, tagBdL_single, Finsupp.linearCombination_single, one_smul]

/-- **`∂ ∘ ∂ = 0` in a single slot.** -/
theorem tagBdL_tagBdL (τ : TagSimp X) :
    tagBdL K X (tagBdL K X (Finsupp.single τ (1 : K))) = 0 := by
  obtain ⟨n, σ⟩ := τ
  rw [tagBdL_single]
  match n, σ with
  | 0, _ => rw [tagBd_zero, map_zero]
  | 1, σ =>
      -- every tag produced sits in degree `0`, where `tagBd` vanishes
      rw [tagBd_succ, tagBdL_tagAt]
      have hfun : (fun σ' : singularSimplices X 0 => tagBd K X (⟨0, σ'⟩ : TagSimp X))
          = fun _ => (0 : TagSimp X →₀ K) := funext fun σ' => tagBd_zero K X σ'
      rw [hfun, linearCombinationR_zero_fun]
  | (n + 2), σ =>
      rw [tagBd_succ, tagBdL_tagAt]
      -- `tagBd` at degree `n+1` IS this composite, definitionally, because the
      -- definition is the retagged differential; so `hfun` is `rfl` and the
      -- rewrite has nothing to unify.
      have hfun : (fun σ' : singularSimplices X (n + 1) =>
            tagBd K X (⟨n + 1, σ'⟩ : TagSimp X))
          = fun σ' => (tagAt K X n) ((((singFreeR K).obj X).d (n + 1) n).hom
              (Finsupp.single σ' (1 : K))) := rfl
      rw [hfun]
      -- The goal spells the top degree `n + 1 + 1`, not `n + 2`, and that number
      -- is inside the TYPE of a `ModuleCat` object, so `rw` cannot cross it.
      -- Read off the goal rather than assumed; the two are equal by definition
      -- and not as terms.
      have key := linearCombinationR_comp_single
        ((tagAt K X n).comp ((((singFreeR K).obj X).d (n + 1) n).hom))
        ((((singFreeR K).obj X).d (n + 1 + 1) (n + 1)).hom (Finsupp.single σ (1 : K)))
      rw [show (fun σ' : singularSimplices X (n + 1) =>
            (tagAt K X n) ((((singFreeR K).obj X).d (n + 1) n).hom
              (Finsupp.single σ' (1 : K))))
          = fun σ' => ((tagAt K X n).comp
              ((((singFreeR K).obj X).d (n + 1) n).hom)) (Finsupp.single σ' (1 : K)) from rfl,
        key, LinearMap.comp_apply]
      have hdd := congrArg (fun (g : (((singFreeR K).obj X).X (n + 1 + 1))
          ⟶ (((singFreeR K).obj X).X n)) => g.hom (Finsupp.single σ (1 : K)))
        (HomologicalComplex.d_comp_d ((singFreeR K).obj X) (n + 1 + 1) (n + 1) n)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] at hdd
      rw [hdd, map_zero]

end

end GroupApproximation.CharClass
