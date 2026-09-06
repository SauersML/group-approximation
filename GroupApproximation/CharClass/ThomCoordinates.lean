import GroupApproximation.CharClass.LIXThomClassTerm

/-!
# The Thom class in coordinates

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

First step of `hres` by the point route.  The Thom class is *defined* as the
inverse image of the unit under `ThomDeg.thomEquiv`, so its coordinates are
whatever `thomLift` produces: the top one is the unit and the rest are the Chern
coefficients acting on it.  Reading that off is `jm_thomEquiv_symm`, and it is
what the restriction to the fibre will be applied to.

Nothing here is topology.  The point of stating it is that every later step
computes with the coordinates, and the fact that they are `thomLift` of the unit
is the only thing about the Thom class any of them uses.

## Main declarations

* `ThomDeg.jm_thomEquiv_symm` — the coordinates of the Thom class, in general.
* `thomJmTotal_lixThomClassTerm` — at the mapping-torus bundle.
-/

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace ThomDeg

variable {R : Type} [CommRing R] {r : ℕ} {M : Fin (r + 1) → Type}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable (g : ∀ i : Fin r, M (Fin.last r) →ₗ[R] M i.castSucc)

/-- **The coordinates of the Thom class.**  `thomEquiv` is built from `thomLift`,
so the class it names has exactly `thomLift`'s coordinates. -/
theorem jm_thomEquiv_symm {P : Type} [AddCommGroup P] [Module R P]
    (jm : P →ₗ[R] (∀ i, M i)) (hinj : Function.Injective jm)
    (hrange : LinearMap.range jm = LinearMap.ker (restrictMap g))
    (x : M (Fin.last r)) :
    jm ((thomEquiv g jm hinj hrange).symm x) = thomLift g x := by
  have h : (kerEquiv g) x
      = (LinearEquiv.ofEq _ _ hrange)
        ((LinearEquiv.ofInjective jm hinj)
          ((thomEquiv g jm hinj hrange).symm x)) := by
    conv_lhs => rw [← (thomEquiv g jm hinj hrange).apply_symm_apply x]
    exact (kerEquiv g).apply_symm_apply _
  have h2 := congrArg (fun y : LinearMap.ker (restrictMap g) => (y : ∀ i, M i)) h
  simpa [kerEquiv] using h2.symm

end ThomDeg

end

end GroupApproximation.CharClass
