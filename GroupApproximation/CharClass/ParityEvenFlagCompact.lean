import GroupApproximation.CharClass.ParityEvenFlag
import GroupApproximation.CharClass.LerayHirschCompact
import GroupApproximation.CharClass.RelativeBundleNonempty

/-!
# The flag tower's pullback injectivity, unconditionally

`ParityEvenFlag` reduces injectivity of the flag pullback to the per-stage
projective-bundle statement.  This file discharges that statement at every stage
from `cc-projective`'s `LH.lerayHirschGraded_compact`, so the tower's injectivity
carries no hypothesis beyond compactness, non-emptiness and constant rank of the
base — all of which the LIX mapping torus has.

## The three side conditions, and where each comes from

* **Compact** at every stage: `flag_compactSpace`, by induction through
  `cc-bundle`'s `flagZero` and `flagSucc` and `Bundle.Proj.instCompactSpace`.
* **Non-empty** at every stage below the top: `flag_nonempty`, the same induction
  with `cc-relative`'s `RelativeSupport.nonempty_proj_of_forall`, whose rank
  positivity comes from the additive `rank_flagRest`.
* **Constant rank** at stage `n`: `flagRest_rank_eq`, again `rank_flagRest`.  The
  additive form `rank + n = r` is what makes both this and the positivity above
  free of natural subtraction; the subtractive form would need `n ≤ r` carried
  everywhere and would truncate at the top.

`n < r` is used for positivity and for `1 ≤ r - n`, and it is exactly the range
`ParityEvenFlag`'s per-stage hypothesis is asked over — at `n ≥ r` the rest bundle
has rank zero and `lerayHirschGraded_compact` does not apply.
-/

set_option autoImplicit false

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Wu

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- Every stage of the flag tower is compact when the base is. -/
theorem flag_compactSpace [CompactSpace X] (p : Bundle X ι) (n : ℕ) :
    CompactSpace (Bundle.Flag p n) := by
  induction n with
  | zero => exact (Bundle.flagZero p).symm.compactSpace
  | succ n ih =>
    haveI := ih
    exact (Bundle.flagSucc p n).symm.compactSpace

/-- The rank of the rest bundle at stage `n`, in the additive form. -/
theorem flagRest_rank_eq (p : Bundle X ι) (r : ℕ) (hr : ∀ x, p.rank x = r) (n : ℕ)
    (w : Bundle.Flag p n) : (Bundle.flagRest p n).rank w + n = r := by
  have h := Bundle.rank_flagRest p n w
  rw [hr (Bundle.flagProj p n w)] at h
  exact h

/-- Every stage of the tower up to the top is non-empty. -/
theorem flag_nonempty [CompactSpace X] [Nonempty X] (p : Bundle X ι) (r : ℕ)
    (hr : ∀ x, p.rank x = r) : ∀ n : ℕ, n ≤ r → Nonempty (Bundle.Flag p n) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨(Bundle.flagZero p).symm (Classical.arbitrary X)⟩
  | succ n ih =>
    intro hn
    haveI := ih (by omega)
    haveI := flag_compactSpace p n
    have hpos : ∀ w : Bundle.Flag p n, 0 < (Bundle.flagRest p n).rank w := by
      intro w
      have h := flagRest_rank_eq p r hr n w
      omega
    haveI : Nonempty (Bundle.Proj (Bundle.flagRest p n)) :=
      RelativeSupport.nonempty_proj_of_forall (Bundle.flagRest p n) hpos
    exact ⟨(Bundle.flagSucc p n).symm (Classical.arbitrary _)⟩

/-- **The per-stage input, discharged.**  At stage `n < r` the rest bundle has
constant rank `r - n ≥ 1` over a compact non-empty base, so `cc-projective`'s
Leray–Hirsch applies and its `pull_injective` lifts to the ring. -/
theorem flagRest_map_injective [DecidableEq ι] [CompactSpace X] [Nonempty X] (p : Bundle X ι)
    (r : ℕ) (hr : ∀ x, p.rank x = r) (n : ℕ) (hn : n < r) :
    Function.Injective (TotalH.map (cmap (Bundle.projPi (Bundle.flagRest p n)))) := by
  haveI := flag_compactSpace p n
  haveI := flag_nonempty p r hr n (by omega)
  refine totalH_map_injective _ ?_
  intro k
  exact (LH.lerayHirschGraded_compact (Bundle.flagRest p n) (r - n)
    (fun w => by have h := flagRest_rank_eq p r hr n w; omega) (by omega)).pull_injective
    (by omega) k

/-- **The flag pullback is injective, unconditionally.**  Nothing is left as a
hypothesis except what the LIX mapping torus has: a compact non-empty base and
constant rank. -/
theorem flagProj_map_injective_compact [DecidableEq ι] [CompactSpace X] [Nonempty X]
    (p : Bundle X ι)
    (r : ℕ) (hr : ∀ x, p.rank x = r) :
    Function.Injective (TotalH.map (cmap (Bundle.flagProj p r))) :=
  flagProj_map_injective_of_proj p r
    (fun n hn => flagRest_map_injective p r hr n hn)

end

end Wu
end CharClass
end GroupApproximation
