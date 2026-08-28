import GroupApproximation.Sofic.SmallCancellationRouter

/-!
# The Greendlinger conclusion gives a linear isoperimetric inequality

`Sofic/SmallCancellationRouter.lean` states `GreendlingerConclusion R`: every
reduced nonempty word in the relator subgroup contains a subword that is more
than half of some symmetrized relator.  That is Dehn's condition, and the
seventy-odd `Sofic/Greendlinger*` modules exist to prove it for metric small
cancellation.

This module spends it on the next classical step: **a Dehn condition gives a
linear isoperimetric inequality, with constant one**.  The proof is an
induction on word length and uses no van Kampen diagram, because area is taken
in its algebraic form --- the number of conjugates of relators a product needs
--- rather than as the face count of a planar diagram.  Van Kampen's lemma is
then not needed at all: it is the statement that the two agree.

## The step

Let `w` be reduced, nonempty, and trivial in the quotient.  Dehn's condition
gives a symmetrized relator `r = u ++ v` and a decomposition `w = a ++ u ++ b`
with `|r| < 2|u|`, so `|v| < |u|`.  In the free group

```
    mk w = (mk a * mk r * (mk a)⁻¹) * mk (a ++ invRev v ++ b) ,
```

one conjugate of one relator times a strictly shorter word --- shorter because
`|a| + |v| + |b| < |a| + |u| + |b|`.  Iterating costs one relator per letter
removed, so `area(g) ≤ |g|`.

## What this is for

It is the middle third of the standard route from a small-cancellation
hypothesis to hyperbolicity: small cancellation gives Dehn's condition (the
`Greendlinger*` lane, for `C'(λ)`; a diagram lane would be needed for the
non-metric `C(3)`-`T(8)` conditions), Dehn's condition gives the linear
isoperimetric inequality (here), and the linear isoperimetric inequality gives
thin triangles (Gromov; not proved in this repository).  The last third then
meets `Algebra/HyperbolicSlimFourPoint.lean`, which turns thin triangles into
`Hyperbolic.IsHyperbolicGroup`.

`IsConjugateProduct` counts conjugates of *symmetrized* relators, which is why
no inverses appear in it: `symmetrization` is already closed under formal
inversion, and `normalClosure_symmetrization` says the two relator families
generate the same normal subgroup.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Algebraic area -/

/-- **`g` is a product of `n` conjugates of members of `R`.**  This is the
area of `g` in its algebraic form: no planarity, no diagram, and van Kampen's
lemma is not needed to state it. -/
def IsConjugateProduct (R : Set (FreeGroup α)) : ℕ → FreeGroup α → Prop
  | 0, g => g = 1
  | n + 1, g => ∃ c s h : FreeGroup α,
      s ∈ R ∧ g = c * s * c⁻¹ * h ∧ IsConjugateProduct R n h

/-- **The linear isoperimetric inequality** at constant `K`: every element of
the relator subgroup is a product of at most `K * |g|` conjugates of
relators. -/
def LinearIsoperimetric (R : Set (FreeGroup α)) (K : ℕ) : Prop :=
  ∀ g ∈ Subgroup.normalClosure R,
    ∃ n ≤ K * FreeGroup.norm g, IsConjugateProduct R n g

/-! ## Dehn's condition pays for it -/

/-- **A Greendlinger conclusion gives a linear isoperimetric inequality with
constant one.**

Induction on the length of the reduced word: one Dehn step removes one
conjugate of one relator and shortens the word, so the number of relators a
product needs is at most its length.  Nothing here is metric --- the input is
the Dehn condition itself, so any lane that establishes it, for metric or
non-metric small cancellation, pays for the inequality at once. -/
theorem linearIsoperimetric_of_greendlinger [DecidableEq α]
    {R : Set (List (α × Bool))} (hG : GreendlingerConclusion R) :
    LinearIsoperimetric (FreeGroup.mk '' symmetrization R) 1 := by
  have key : ∀ N : ℕ, ∀ g : FreeGroup α,
      FreeGroup.norm g ≤ N →
      g ∈ Subgroup.normalClosure (FreeGroup.mk '' R) →
      ∃ n ≤ FreeGroup.norm g,
        IsConjugateProduct (FreeGroup.mk '' symmetrization R) n g := by
    intro N
    induction N with
    | zero =>
        intro g hle hmem
        have hnorm : FreeGroup.norm g = g.toWord.length := rfl
        have hlen : g.toWord.length = 0 := by omega
        have hg : g = 1 :=
          FreeGroup.toWord_eq_nil_iff.mp (List.eq_nil_of_length_eq_zero hlen)
        exact ⟨0, Nat.zero_le _, hg⟩
    | succ N ih =>
        intro g hle hmem
        by_cases hg : g = 1
        · exact ⟨0, Nat.zero_le _, hg⟩
        · have hred : FreeGroup.IsReduced g.toWord := FreeGroup.isReduced_toWord
          have hne : g.toWord ≠ [] := fun h => hg (FreeGroup.toWord_eq_nil_iff.mp h)
          have hmem' : FreeGroup.mk g.toWord ∈
              Subgroup.normalClosure (FreeGroup.mk '' R) := by
            rw [FreeGroup.mk_toWord]
            exact hmem
          obtain ⟨r, hr, u, hu_inf, hu_pre, hlen⟩ := hG g.toWord hred hne hmem'
          obtain ⟨a, b, hab⟩ := hu_inf
          obtain ⟨v, hv⟩ := hu_pre
          -- the shortened word and the identity that produces it
          have e_r : FreeGroup.mk r = FreeGroup.mk u * FreeGroup.mk v := by
            rw [FreeGroup.mul_mk, hv]
          have e_g : g = FreeGroup.mk a * FreeGroup.mk u * FreeGroup.mk b := by
            have h1 : FreeGroup.mk (a ++ u ++ b) = g := by
              rw [hab, FreeGroup.mk_toWord]
            rw [← h1, FreeGroup.mul_mk, FreeGroup.mul_mk]
          have e_g' : FreeGroup.mk (a ++ FreeGroup.invRev v ++ b)
              = FreeGroup.mk a * (FreeGroup.mk v)⁻¹ * FreeGroup.mk b := by
            rw [FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.mul_mk]
          have hsplit : g = (FreeGroup.mk a * FreeGroup.mk r * (FreeGroup.mk a)⁻¹)
              * FreeGroup.mk (a ++ FreeGroup.invRev v ++ b) := by
            rw [e_g, e_g', e_r]
            group
          -- it is strictly shorter
          have hvu : v.length < u.length := by
            have h6 : (u ++ v).length = u.length + v.length := List.length_append
            rw [hv] at h6
            omega
          have hnorm' : FreeGroup.norm (FreeGroup.mk (a ++ FreeGroup.invRev v ++ b))
              < FreeGroup.norm g := by
            have h1 : FreeGroup.norm (FreeGroup.mk (a ++ FreeGroup.invRev v ++ b))
                ≤ (a ++ FreeGroup.invRev v ++ b).length := FreeGroup.norm_mk_le _
            have h2 : (a ++ FreeGroup.invRev v ++ b).length
                = a.length + v.length + b.length := by
              simp [FreeGroup.invRev]
            have h3 : FreeGroup.norm g = g.toWord.length := rfl
            have h4 : g.toWord.length = a.length + u.length + b.length := by
              rw [← hab]
              simp
            omega
          -- and it still lies in the relator subgroup
          have hrmem : FreeGroup.mk r ∈ Subgroup.normalClosure (FreeGroup.mk '' R) := by
            rw [← normalClosure_symmetrization]
            exact Subgroup.subset_normalClosure ⟨r, hr, rfl⟩
          have hconj : FreeGroup.mk a * FreeGroup.mk r * (FreeGroup.mk a)⁻¹
              ∈ Subgroup.normalClosure (FreeGroup.mk '' R) :=
            (inferInstance :
              (Subgroup.normalClosure (FreeGroup.mk '' R)).Normal).conj_mem _ hrmem _
          have hmemg' : FreeGroup.mk (a ++ FreeGroup.invRev v ++ b)
              ∈ Subgroup.normalClosure (FreeGroup.mk '' R) := by
            have hrewrite : FreeGroup.mk (a ++ FreeGroup.invRev v ++ b)
                = (FreeGroup.mk a * FreeGroup.mk r * (FreeGroup.mk a)⁻¹)⁻¹ * g := by
              rw [hsplit]
              group
            rw [hrewrite]
            exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hconj) hmem
          obtain ⟨n, hn_le, hn⟩ :=
            ih (FreeGroup.mk (a ++ FreeGroup.invRev v ++ b)) (by omega) hmemg'
          refine ⟨n + 1, by omega, ?_⟩
          show ∃ c s h : FreeGroup α,
            s ∈ FreeGroup.mk '' symmetrization R ∧ g = c * s * c⁻¹ * h ∧
              IsConjugateProduct (FreeGroup.mk '' symmetrization R) n h
          exact ⟨FreeGroup.mk a, FreeGroup.mk r,
            FreeGroup.mk (a ++ FreeGroup.invRev v ++ b), ⟨r, hr, rfl⟩, hsplit, hn⟩
  intro g hg
  have hmem : g ∈ Subgroup.normalClosure (FreeGroup.mk '' R) := by
    rwa [normalClosure_symmetrization] at hg
  obtain ⟨n, hn_le, hn⟩ := key (FreeGroup.norm g) g le_rfl hmem
  exact ⟨n, by omega, hn⟩

end SmallCancellationRouter
end GroupApproximation
