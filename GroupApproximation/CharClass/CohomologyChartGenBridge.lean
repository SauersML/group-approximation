import GroupApproximation.CharClass.CohomologyChartInduction

/-!
# From Gysin surjectivity to the product form

`CohomologyChartInduction` reduces the projective-factor Künneth over an
arbitrary base to `KnCP.CPGenHyp`, which cups the generator on the **left**.  The
Gysin layer produces the same statement with the generator on the **right**:
`GysinData.bijective_cupRight` says `cupRightE e n`, that is `y ↦ y ⌣ e`, is
bijective.  Over `F₂` the two differ by nothing but a degree cast, and this file
is that cast, written once so that no consumer has to write it.

The reason it is worth a file of its own is that the cast is not the obvious one.
`cup_comm` produces `cohCast (Nat.add_comm q p)`, so the two sides of the bridge
carry casts in opposite directions, and composing them is what collapses to the
identity.

## Main declarations

* `KnCP.cpGenHyp_of_cup_right_surjective` — the bridge, from the bare surjectivity
  statement, so a consumer needs no Gysin structure to use it.
* `KnCP.cpGenHyp_of_bijective_cupRight` — the same from the shape
  `GysinData.bijective_cupRight` returns.
* `KnCP.cpSplit_of_cup_right_surjective` — **the whole chain in one application**:
  Gysin surjectivity on the fibres gives the product form over every base.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

/-- **The bridge.**  Cupping the generator on the right is surjective if and only
if cupping it on the left is, and `CPGenHyp` is the left version. -/
theorem cpGenHyp_of_cup_right_surjective (d : ℕ)
    (hsurj : ∀ (hd : 1 ≤ d) (n : ℕ) (c : Hmod2 (CPtop d) (n + 2)),
      ∃ b : Hmod2 (CPtop d) n, c = cup b (cpGen d hd)) :
    CPGenHyp d := by
  intro hd k c
  obtain ⟨b, hb⟩ := hsurj hd k (cohCast (Nat.add_comm 2 k) c)
  refine ⟨b, ?_⟩
  have h := congrArg (cohCast (Nat.add_comm k 2)) hb
  rw [cohCast_cohCast, cohCast_self, cup_comm b (cpGen d hd), cohCast_cohCast,
    cohCast_self] at h
  exact h

/-- The bridge in the shape the Gysin layer hands over.  `GysinData` for the
tautological bundle over `ℂP^d` gives exactly this. -/
theorem cpGenHyp_of_bijective_cupRight (d : ℕ)
    (hbij : ∀ (hd : 1 ≤ d) (n : ℕ), Function.Surjective (cupRightE (cpGen d hd) n)) :
    CPGenHyp d :=
  cpGenHyp_of_cup_right_surjective d (fun hd n c => by
    obtain ⟨b, hb⟩ := hbij hd n c
    exact ⟨b, hb.symm⟩)

/-- **The projective-factor Künneth over an arbitrary base, from Gysin
surjectivity on the fibres alone.**  This is the whole chain: the fibre statement
is about `ℂP^e` with no base in it, and the conclusion is about `U × ℂP^e` for
every `U`.  Rank one is not asked for, because it is the base of the induction and
is unconditional. -/
theorem cpSplit_of_cup_right_surjective
    (hsurj : ∀ e : ℕ, 2 ≤ e → ∀ (hd : 1 ≤ e) (n : ℕ) (c : Hmod2 (CPtop e) (n + 2)),
      ∃ b : Hmod2 (CPtop e) n, c = cup b (cpGen e hd)) :
    ∀ e : ℕ, 1 ≤ e → CPSplit e :=
  cpSplit_of_cpGenHyp (fun e he => cpGenHyp_of_cup_right_surjective e (hsurj e he))

end KnCP

end

end GroupApproximation.CharClass
