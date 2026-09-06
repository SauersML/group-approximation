import GroupApproximation.CharClass.ThomStepCEuler
import GroupApproximation.CharClass.ThomFreeDegreewise

/-!
# The residual of Step C, named exactly

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C, hypothesis 6).

`ThomStepCEuler.lean` reduced the last open hypothesis of Step C from an
identification of two classes to a nonvanishing, `su ≠ 0`.  This file splits that
nonvanishing into the two facts it is actually made of, so that what remains is
named and localised rather than carried as one opaque hypothesis about the
manuscript's section.

```text
su = σ^* u ≠ 0      ⟸      u ≠ 0      and      σ^* does not kill u.
```

* **`u ≠ 0` is free.**  `ThomFreeDegreewise.thomEquiv` says the relative group of
  the pair is `H^0(X; F₂)` with the Thom class the image of a chosen top
  coefficient, so the Thom class is nonzero as soon as that coefficient is —
  `thomClass_ne_zero` below.  Nothing topological is used.
* **`σ^*` not killing it is the whole residual**, and it is a statement about the
  *section*, not about the Thom class.  It is where the zero being nondegenerate
  enters, through `eulerLocalHomeo`, whose derivative is invertible: the section
  is then a homeomorphism of punctured pairs near its zero, and mod 2 a
  homeomorphism of pairs induces an isomorphism, with no degree computation.

`SectionDetectsThom` names that residual as a one-field predicate about a single
morphism.  It is deliberately weaker than "`σ^*` is injective", because only its
value on the Thom line is ever needed.

## What is left of Step C, in full

1. The Leray–Hirsch instance for the projectivised bundle — `cc-projective`.
2. The tautological class of `P(E⊕1)` restricts to that of `P(E)` — `cc-projective`.
3. `SectionDetectsThom` for the manuscript's section — this lane, from
   `eulerLocalHomeo` and `relCohomologyCongrPoint`, once the bundle's
   trivialisation over the chart is available.

## Main declarations

* `thomClass_ne_zero` — the Thom class is nonzero, from `thomEquiv` alone.
* `SectionDetectsThom`, `su_ne_zero_of_section` — the residual, named.
* `topChernClass_ne_zero_of_section` — Step C over items 1–3 only.
-/

open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. The Thom class is nonzero, for free -/

/-- **The Thom class is nonzero.**  `thomEquiv` identifies the relative group of
the pair with the top Leray–Hirsch coefficient group, so a nonzero coefficient
gives a nonzero class.  No topology: this is the linear algebra of
`ThomFreeDegreewise` read backwards. -/
theorem thomClass_ne_zero {R : Type} [CommRing R] {r : ℕ} {M : Fin (r + 1) → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (g : ∀ i : Fin r, M (Fin.last r) →ₗ[R] M i.castSucc)
    {P : Type} [AddCommGroup P] [Module R P]
    (jm : P →ₗ[R] (∀ i, M i)) (hinj : Function.Injective jm)
    (hrange : LinearMap.range jm = LinearMap.ker (ThomDeg.restrictMap g))
    {x : M (Fin.last r)} (hx : x ≠ 0) :
    (ThomDeg.thomEquiv g jm hinj hrange).symm x ≠ 0 := by
  intro h
  refine hx ?_
  have := congrArg (ThomDeg.thomEquiv g jm hinj hrange) h
  rwa [LinearEquiv.apply_symm_apply, map_zero] at this

/-! ## 2. The residual, named -/

/-- **The residual of Step C.**  The section pullback does not kill the Thom
class.  This is deliberately weaker than injectivity of `sRel`: only the value on
the Thom line is ever used, and only that value is what the local homeomorphism
at the zero controls. -/
def SectionDetectsThom {HrelE rel : ModuleCat.{0} (ZMod 2)}
    (sRel : HrelE ⟶ rel) (u : HrelE) : Prop :=
  sRel.hom u ≠ 0

/-- The relative Euler class is nonzero exactly when the section detects the Thom
class.  This is a restatement, and it is the point: the residual is a property of
the *section*, not of the Thom class or of the excision chain. -/
theorem su_ne_zero_of_section {HrelE rel : ModuleCat.{0} (ZMod 2)}
    (sRel : HrelE ⟶ rel) {u : HrelE} (h : SectionDetectsThom sRel u) :
    sRel.hom u ≠ 0 := h

/-! ## 3. Step C over the named residual -/

variable {N : Type} [TopologicalSpace N] {twoR : ℕ} {z : N}

/-- **Step C over the residual list.**  Every hypothesis of
`topChernClass_ne_zero_of_chain` is now either discharged inside this lane, or
supplied by `cc-relative`, or one of the three items in the module docstring.
The only one about the manuscript's geometry is `SectionDetectsThom`. -/
theorem topChernClass_ne_zero_of_section (hacyclic : PuncturedAcyclic N twoR z)
    {rel chart HrelE : ModuleCat.{0} (ZMod 2)} {r : ℕ}
    (j : rel ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (i : cohomologyZMod2 (TopCat.of N) twoR
          ⟶ cohomologyZMod2 (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absLine : Nonempty (cohomologyZMod2 (TopCat.of N) twoR ≃ₗ[ZMod 2] ZMod 2))
    (exc : rel ≅ chart)
    (chartIso : chart ≅
      relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    (sRel : HrelE ⟶ rel) {u : HrelE} (hdetect : SectionDetectsThom sRel u)
    {gamma : cohomologyZMod2 (TopCat.of N) twoR} (hgamma : gamma = j.hom (sRel.hom u)) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_of_su_ne_zero_line hacyclic j i hexact absLine exc chartIso
    (su_ne_zero_of_section sRel hdetect) hgamma

/-! The axiom list, printed on every build. -/

#print axioms topChernClass_ne_zero_of_section

end

end GroupApproximation.CharClass
