import GroupApproximation.CharClass.ThomStepCOddLocal

/-!
# `hne` from the injectivity the odd side already needs

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`LemmaTwoStepCThom.ThomChainThom` has a field `hne : sRel.hom u ≠ 0`, the
nonvanishing of the Thom class **after** the section, and `cc-projective`'s
seam audit found that `cc-thom`'s `u ≠ 0` does not produce it: a linear map kills
zero, so the image statement is strictly stronger and the implication runs the
wrong way.

It costs nothing extra all the same, because the missing content is exactly the
injectivity of `sRel` that the odd side needs anyway.  Injectivity of a composite
gives injectivity of its first factor, so the same `hinj` that
`ThomStepCOdd.topChernClass_ne_zero_odd` takes, or the same `res`/`hsq`/`hres`
that `ThomStepCOddLocal` takes, delivers `hne` with no further topology.

So the audit's finding stands and the fix does not add an obligation: it moves
`hne` from "open, owner unassigned" to "closed by whoever closes `hinj`".

## Main declarations

* `injective_of_comp_injective` — injectivity passes to the first factor.
* `ne_zero_of_injective_comp` — **`hne` from `hinj` and `u ≠ 0`.**
* `ne_zero_of_local` — **`hne` from the local restriction data.**
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {A B C D : ModuleCat.{0} (ZMod 2)}

/-- **Injectivity of a composite passes to its first factor.** -/
theorem injective_of_comp_injective (sRel : A ⟶ B) (t : B ⟶ D)
    (hinj : Function.Injective (sRel ≫ t).hom) : Function.Injective sRel.hom := by
  intro x y hxy
  refine hinj ?_
  show t.hom (sRel.hom x) = t.hom (sRel.hom y)
  rw [hxy]

/-- **`hne` from `hinj`.**  The image of a nonzero class under an injective map is
nonzero, and the injectivity is the one the odd side already needs. -/
theorem ne_zero_of_injective_comp (sRel : A ⟶ B) (t : B ⟶ D)
    (hinj : Function.Injective (sRel ≫ t).hom) {u : A} (hu : u ≠ 0) :
    sRel.hom u ≠ 0 := by
  intro h0
  refine hu (injective_of_comp_injective sRel t hinj ?_)
  rw [h0, map_zero]

/-- **`hne` from the local restriction data**, in the shape
`ThomStepCOddLocal.topChernClass_ne_zero_odd_local` takes it.  So a producer of
that theorem's hypotheses gets `ThomChainThom.hne` for free. -/
theorem ne_zero_of_local (sRel : A ⟶ B) (t : B ⟶ D) (res : A ⟶ C) (loc : C ≅ D)
    (hsq : sRel ≫ t = res ≫ loc.hom) (hres : Function.Injective res.hom)
    {u : A} (hu : u ≠ 0) : sRel.hom u ≠ 0 :=
  ne_zero_of_injective_comp sRel t (injective_comp_of_square sRel t res loc hsq hres) hu

/-! Printed on every build. -/

#print axioms ne_zero_of_local

end

end GroupApproximation.CharClass
