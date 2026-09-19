import GroupApproximation.CharClass.ParityEvenTransport
import GroupApproximation.CharClass.BundleFlagStage

/-!
# Injectivity of the flag pullback, from the per-stage statement

`Wu.SplittingData.pull_injective` asks for `Function.Injective (TotalH.map proj)`
where `proj` is the projection of the **flag** space.  That is the only thing the
field needs, and it is the only thing that can be supplied: a `LerayHirschGraded`
for the flag projection does not exist, because the cohomology of a flag space is
free over the base on monomials in several classes rather than on powers of one.

What *is* available is Leray–Hirsch one stage at a time.  `cc-bundle`'s
`flagSucc p n : Flag p (n+1) ≃ₜ Proj (flagRest p n)` identifies each stage as the
projective bundle of the rest bundle over the previous stage, and each of those is
a projective bundle over a compact base.  This file composes those into injectivity
for the whole tower, using nothing but

* `Wu.totalH_map_injective_of_iso` — pullback along an isomorphism is injective;
* `Wu.totalH_map_injective_comp` — injectivity composes along `≫`.

Neither takes a compactness or non-emptiness hypothesis: those live entirely in the
per-stage invocations of `lerayHirschGraded_of_trivializing_cover` and do not
propagate into the ring-level assembly.

## Main results

* `flagProj_zero_map_injective` — the base case, from `cc-bundle`'s `flagZero`.
* `flagForget_map_injective` — one stage, from the projective-bundle statement.
* `flagProj_map_injective`, `flagProj_map_injective_of_proj` — the whole tower.
-/

set_option autoImplicit false

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Wu

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- **Injectivity from a continuous left inverse.**  Stated with `cmap` only: going
through `TopCat.isoOfHomeo` and `Iso.hom` instead exhausts the heartbeat budget on
these spaces, because the unifier has to whnf `Proj (flagRest p n)`, whose defining
predicate mentions the rest bundle applied at points. -/
theorem totalH_map_injective_of_leftInv {A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] (f : C(A, B)) (g : C(B, A)) (hfg : ∀ b, f (g b) = b) :
    Function.Injective (TotalH.map (cmap f)) := by
  have hcomp : cmap g ≫ cmap f = 𝟙 (TopCat.of B) := by
    apply TopCat.ext
    intro b
    exact hfg b
  intro c c' hcc
  have h2 := congrArg (TotalH.map (cmap g)) hcc
  rw [← totalH_map_comp, ← totalH_map_comp, hcomp, totalH_map_id, totalH_map_id] at h2
  exact h2

/-- One stage of the tower: the forgetful map is the projection of the rest
bundle, read through `cc-bundle`'s `flagSucc`.  The morphism identity is proved
pointwise with `TopCat.ext` from `flagSucc_over_base`. -/
theorem flagForget_map_injective (p : Bundle X ι) (n : ℕ)
    (h : Function.Injective
      (TotalH.map (cmap (Bundle.projPi (Bundle.flagRest p n))))) :
    Function.Injective (TotalH.map (cmap (Bundle.flagForget p n))) := by
  have hfe : cmap (Bundle.flagForget p n)
      = cmap (Bundle.flagSucc p n) ≫ cmap (Bundle.projPi (Bundle.flagRest p n)) := by
    apply TopCat.ext
    intro w
    exact (Bundle.flagSucc_over_base p n w).symm
  rw [hfe]
  refine totalH_map_injective_comp _ _ ?_ h
  exact totalH_map_injective_of_leftInv _ (Bundle.flagSucc p n).symm
    (fun b => (Bundle.flagSucc p n).apply_symm_apply b)

/-- The zeroth stage is the base: `flagSet p 0` forces the line family to vanish, so
`flagProj p 0` is `cc-bundle`'s `flagZero`. -/
theorem flagProj_zero_map_injective (p : Bundle X ι) :
    Function.Injective (TotalH.map (cmap (Bundle.flagProj p 0))) :=
  totalH_map_injective_of_leftInv _ (Bundle.flagZero p).symm
    (fun x => by
      rw [← Bundle.flagZero_eq_flagProj]
      exact (Bundle.flagZero p).apply_symm_apply x)

/-- **The whole tower.**  The per-stage hypothesis is asked for only at the stages
the induction to height `r` actually consumes, `n < r`.  Asking for all `n` would be
an over-ask, and worse: at `n ≥ r` the rest bundle has rank zero, where the
projective-bundle statement is not available at all. -/
theorem flagProj_map_injective (p : Bundle X ι) :
    ∀ r : ℕ, (∀ n : ℕ, n < r →
        Function.Injective (TotalH.map (cmap (Bundle.flagForget p n)))) →
      Function.Injective (TotalH.map (cmap (Bundle.flagProj p r))) := by
  intro r
  induction r with
  | zero => intro _; exact flagProj_zero_map_injective p
  | succ r ih =>
    intro hstage
    have hcomp : cmap (Bundle.flagProj p (r + 1))
        = cmap (Bundle.flagForget p r) ≫ cmap (Bundle.flagProj p r) := by
      apply TopCat.ext
      intro w
      rfl
    rw [hcomp]
    exact totalH_map_injective_comp _ _ (hstage r (by omega))
      (ih fun n hn => hstage n (by omega))

/-- The tower, with the per-stage input in the projective-bundle form
`cc-projective`'s Leray–Hirsch actually produces. -/
theorem flagProj_map_injective_of_proj (p : Bundle X ι) (r : ℕ)
    (hproj : ∀ n : ℕ, n < r → Function.Injective
      (TotalH.map (cmap (Bundle.projPi (Bundle.flagRest p n))))) :
    Function.Injective (TotalH.map (cmap (Bundle.flagProj p r))) :=
  flagProj_map_injective p r (fun n hn => flagForget_map_injective p n (hproj n hn))

end

end Wu
end CharClass
end GroupApproximation
