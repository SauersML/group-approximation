import GroupApproximation.CharClass.SliceRootsOf
import GroupApproximation.CharClass.SliceNaturalOf
import GroupApproximation.CharClass.ChernSplittingOfFlagRelation
import GroupApproximation.Meta.AxiomGuard

/-!
# The slice value of `V` over a field `K`, at sphere rank `n`

Lane `lx-sliceK` of the STW Problem LIX strongest-theorem swarm; the coefficient-generic form of
`SliceSplitV` and `SliceValueV`, and the `slice` field of `Gen.RealBundleModP`.

The split relation for `V = 𝟏^{n+1} ⊕ H` over `K` is `lx-splitK`'s `splitRelation_of_sumOf` at the
flat family of lines (`SliceGenOfLines`).  Its roots are zero on the constant lines and the
pulled-back class of the tautological line on every block line (`SliceRootsOf`), so the Chern
classes are the coefficients of `sliceClass univ gen dd` (`SliceValueVOf`).

The mapping torus lives at a doubled index, and its restriction to the slice is `V` pushed into one
block.  So everything is also stated after pushing along an injection `u`, at the larger index,
and `sliceValue_of_comapOf` is the statement the consumer uses: the Chern classes of a bundle `E`
over `X`, pulled back along `s : Y → X` with `s^* E = u_* V`, are the slice coefficients.

## Main declarations

* `Gen.splitRelation_vBundleYOf`, `Gen.vSliceValueOf` — **the value for `V`.**
* `Gen.sum_pushforward_vLineFlatBundle`, `Gen.splitRelation_pushOf`, `Gen.vSliceValuePushOf` —
  the same after pushing along `u`.
* `Gen.sliceValue_of_comapOf` — **the slice field**, for a bundle whose slice is `u_* V`.
-/

set_option autoImplicit false

noncomputable section

namespace GroupApproximation.CharClass

open CategoryTheory
open scoped Matrix
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.LH

set_option linter.unusedSectionVars false

namespace Gen

/-! ## 1. `V` itself -/

/-- **The split relation for `V` at rank `n`, over `K`**, at the Euler-class roots. -/
theorem splitRelation_vBundleYOf (K : Type) [Field K] (n : ℕ) {ℓ : ℕ} (dd : Fin ℓ → ℕ)
    (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd))) 2) :
    ∏ l ∈ Finset.range (KGen.lixRank n dd),
      (evenTautOf K (LH.tautEulerDualK K hgen (vBundleY n dd))
        + Gen.evenMap K (cmap (projPi (vBundleY n dd)))
            (evenTautOf K (vRootFlatOf K n hgen l))) = 0 :=
  splitRelation_of_sumOf K hgen (vBundleY n dd) (KGen.lixRank n dd) (kgenLixRank_pos n dd)
    (vLineFlatBundle n dd) (fun l => trace_vLineFlatBundle n dd l) (sum_vLineFlatBundle n dd)

/-- **The slice value for `V` over `K`**: the Chern classes of `V = 𝟏^{n+1} ⊕ H` over
`∏ⱼ ℂP^{dⱼ}` are the coefficients of `∏ⱼ (1 + hⱼ X)^{dⱼ}`, with `hⱼ = sliceGenOf K n hgen j`. -/
theorem vSliceValueOf (K : Type) [Field K] (n : ℕ) {ℓ : ℕ} (dd : Fin ℓ → ℕ)
    (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd))) 2)
    (L : LerayHirschGraded (projMapOf (vBundleY n dd)) (LH.tautEulerDualK K hgen (vBundleY n dd))
      (KGen.lixRank n dd)) (q : ℕ) :
    (LerayHirschDataEvenOf.of_graded L).chern q
      = (sliceClass (Finset.univ : Finset (Fin ℓ)) (sliceGenOf K n hgen) dd).coeff q := by
  haveI : Nontrivial (TotalHOf K (TopCat.of (baseY dd))) :=
    @nontrivial_totalHOf K _ _ (TopCat.of (baseY dd)) ⟨baseYPoint dd⟩
  haveI : Nontrivial (Gen.evenPart K (TopCat.of (baseY dd))) := nontrivial_evenPartOf _
  refine (LerayHirschDataEvenOf.of_graded L).chern_eq_sliceClass_coeffOf n dd (vIndexEquiv n dd)
    (vRootFlatOf K n hgen) (splitRelation_vBundleYOf K n dd hgen) (sliceGenOf K n hgen) ?_ ?_ q
  · intro i
    show vRootFlatOf K n hgen ((vIndexEquiv n dd (Sum.inl i) : Fin (KGen.lixRank n dd)) : ℕ) = 0
    rw [vRootFlatOf_equiv, vRootOf_inl]
  · intro b
    show evenTautOf K (vRootFlatOf K n hgen
        ((vIndexEquiv n dd (Sum.inr b) : Fin (KGen.lixRank n dd)) : ℕ))
      = sliceGenOf K n hgen b.1
    rw [vRootFlatOf_equiv]
    exact evenTautOf_vRootOf_inr K n hgen b

/-! ## 2. After pushing `V` into a larger index -/

/-- `V` pushed along an injection is the sum of the pushed lines. -/
theorem sum_pushforward_vLineFlatBundle (n : ℕ) {ℓ : ℕ} (dd : Fin ℓ → ℕ) {κ : Type} [Fintype κ]
    [DecidableEq κ] (u : VIdx n dd → κ) (hu : Function.Injective u) (y : baseY dd) :
    (pushforward u hu (vBundleY n dd)) y
      = ∑ l ∈ Finset.range (KGen.lixRank n dd), (pushforward u hu (vLineFlatBundle n dd l)) y := by
  show coordIncl u * (vBundleY n dd) y * (coordIncl u)ᴴ
    = ∑ l ∈ Finset.range (KGen.lixRank n dd),
        coordIncl u * (vLineFlatBundle n dd l) y * (coordIncl u)ᴴ
  rw [sum_vLineFlatBundle n dd y, Matrix.mul_sum, Matrix.sum_mul]

/-- **The split relation for `V` pushed along `u`**, over `K`, at the pushed roots. -/
theorem splitRelation_pushOf (K : Type) [Field K] (n : ℕ) {ℓ : ℕ} (dd : Fin ℓ → ℕ) {κ : Type}
    [Fintype κ] [DecidableEq κ] (u : VIdx n dd → κ) (hu : Function.Injective u)
    (hgen : Hmod K (CPtop (1 + tautCardOf κ)) 2) :
    ∏ l ∈ Finset.range (KGen.lixRank n dd),
      (evenTautOf K (LH.tautEulerDualK K hgen (pushforward u hu (vBundleY n dd)))
        + Gen.evenMap K (cmap (projPi (pushforward u hu (vBundleY n dd))))
            (evenTautOf K (vRootFlatPushOf K n u hu hgen l))) = 0 :=
  splitRelation_of_sumOf K hgen (pushforward u hu (vBundleY n dd)) (KGen.lixRank n dd)
    (kgenLixRank_pos n dd) (fun l => pushforward u hu (vLineFlatBundle n dd l))
    (fun l => CPn.trace_pushforward_one u hu _ (trace_vLineFlatBundle n dd l))
    (sum_pushforward_vLineFlatBundle n dd u hu)

/-- **The slice value for `V` pushed along `u`**, over `K`. -/
theorem vSliceValuePushOf (K : Type) [Field K] (n : ℕ) {ℓ : ℕ} (dd : Fin ℓ → ℕ) {κ : Type}
    [Fintype κ] [DecidableEq κ] (u : VIdx n dd → κ) (hu : Function.Injective u)
    (hgen : Hmod K (CPtop (1 + tautCardOf κ)) 2)
    (L : LerayHirschGraded (projMapOf (pushforward u hu (vBundleY n dd)))
      (LH.tautEulerDualK K hgen (pushforward u hu (vBundleY n dd))) (KGen.lixRank n dd))
    (q : ℕ) :
    (LerayHirschDataEvenOf.of_graded L).chern q
      = (sliceClass (Finset.univ : Finset (Fin ℓ)) (sliceGenPushOf K n u hu hgen) dd).coeff q := by
  haveI : Nontrivial (TotalHOf K (TopCat.of (baseY dd))) :=
    @nontrivial_totalHOf K _ _ (TopCat.of (baseY dd)) ⟨baseYPoint dd⟩
  haveI : Nontrivial (Gen.evenPart K (TopCat.of (baseY dd))) := nontrivial_evenPartOf _
  refine (LerayHirschDataEvenOf.of_graded L).chern_eq_sliceClass_coeffOf n dd (vIndexEquiv n dd)
    (vRootFlatPushOf K n u hu hgen) (splitRelation_pushOf K n dd u hu hgen)
    (sliceGenPushOf K n u hu hgen) ?_ ?_ q
  · intro i
    show vRootFlatPushOf K n u hu hgen
      ((vIndexEquiv n dd (Sum.inl i) : Fin (KGen.lixRank n dd)) : ℕ) = 0
    rw [vRootFlatPushOf_equiv, vRootPushOf_inl]
  · intro b
    show evenTautOf K (vRootFlatPushOf K n u hu hgen
        ((vIndexEquiv n dd (Sum.inr b) : Fin (KGen.lixRank n dd)) : ℕ))
      = sliceGenPushOf K n u hu hgen b.1
    rw [vRootFlatPushOf_equiv]
    exact evenTautOf_vRootPushOf_inr K n u hu hgen b

/-! ## 3. The slice field -/

/-- **The slice field of the real mod-`p` data.**  For a bundle `E` over `X` whose pullback along
`s : Y → X` is `V` pushed along `u`, the pulled-back Chern classes of `E` are the coefficients of
the slice polynomial. -/
theorem sliceValue_of_comapOf (K : Type) [Field K] (n : ℕ) {ℓ : ℕ} (dd : Fin ℓ → ℕ)
    {X : Type} [TopologicalSpace X] {κ : Type} [Fintype κ] [DecidableEq κ]
    (hgen : Hmod K (CPtop (1 + tautCardOf κ)) 2) (E : Bundle X κ) (s : C(baseY dd, X))
    (u : VIdx n dd → κ) (hu : Function.Injective u)
    (hs : comap s E = pushforward u hu (vBundleY n dd))
    (LE : LerayHirschGraded (projMapOf E) (LH.tautEulerDualK K hgen E) (KGen.lixRank n dd))
    (LV : LerayHirschGraded (projMapOf (pushforward u hu (vBundleY n dd)))
      (LH.tautEulerDualK K hgen (pushforward u hu (vBundleY n dd))) (KGen.lixRank n dd))
    (q : ℕ) :
    Gen.evenMap K (cmap s) ((LerayHirschDataEvenOf.of_graded LE).chern q)
      = (sliceClass (Finset.univ : Finset (Fin ℓ)) (sliceGenPushOf K n u hu hgen) dd).coeff q := by
  haveI : Nonempty (baseY dd) := ⟨baseYPoint dd⟩
  haveI : Nonempty X := ⟨s (baseYPoint dd)⟩
  have Ls : LerayHirschGraded (projMapOf (comap s E)) (LH.tautEulerDualK K hgen (comap s E))
      (KGen.lixRank n dd) := by
    rw [hs]
    exact LV
  have key : ∀ (F : Bundle (baseY dd) κ) (_hF : F = pushforward u hu (vBundleY n dd))
      (LF : LerayHirschGraded (projMapOf F) (LH.tautEulerDualK K hgen F) (KGen.lixRank n dd)),
      (LerayHirschDataEvenOf.of_graded LF).chern q
        = (sliceClass (Finset.univ : Finset (Fin ℓ)) (sliceGenPushOf K n u hu hgen) dd).coeff q := by
    intro F hF LF
    subst hF
    exact vSliceValuePushOf K n dd u hu hgen LF q
  rw [← chern_comap_of_gradedOf K hgen E s LE Ls q]
  exact key _ hs Ls

end Gen

#audit_axioms Gen.vSliceValueOf
#audit_axioms Gen.vSliceValuePushOf
#audit_axioms Gen.sliceValue_of_comapOf

end GroupApproximation.CharClass
