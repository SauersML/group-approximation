import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionAbsorbDominant
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionAbsorbRepeat
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionAbsorbAmplify
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionAbsorbCompactSq

/-!
# Absorption into the corona from compression domination

Lane `TWWSch3c2C3`, work order `WO-TWWSch-3c2-C3`, assembly part. Sources: G. A. Elliott and
D. Kucerovsky, Pacific J. Math. 198 (2001), Thm. 6; G. G. Kasparov, J. Operator Theory 4 (1980),
§7; C. Schafhauser, J. reine angew. Math. 759 (2020), §5. Manuscript label:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (the absorption step).

The corona is `Q(J ⊗ 𝒦) = StdCorona J` with quotient map `π = stdCoronaQuot J`, and the Cuntz pair
is `stdCuntzPair J = (stdCuntzPairBdd J).map π`. The ingredients are:

* the amplification `φ(T) = T ⊗ 1` of `𝓑(H_J)` with `φ ≅ φ ⊕ id`
  (`exists_isBusbyAmplification_stdBdd`, `ExtensionAbsorbAmplify`);
* `T⋆T` compact `⇒` `T` compact (`compactEq_zero_of_star_mul_self`, `ExtensionAbsorbCompactSq`),
  which gives `d⋆d = 0 ⇒ d = 0` in the corona (`stdCorona_eq_zero_of_star_mul_self`);
* the compression form of the Elliott–Kucerovsky swindle
  (`isStronglyAbsorbingBusby_of_amplification_compress`, `ExtensionAbsorbRepeat`);
* compression domination (`BusbyCycle.IsCompressionDominant`, `ExtensionAbsorbDominant`).

Main result: `isStronglyAbsorbingBusby_of_isCompressionDominant`. A unital cycle that dominates by
compression has a strongly absorbing Busby map
`IsStronglyAbsorbingBusby (stdCoronaQuot J) (stdCuntzPair J) 𝒯 (x.busby hx)`, for every family
`𝒯` of unital `⋆`-homomorphisms `S → 𝓑(H_J)`.
-/

noncomputable section

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

section Corona

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **`d⋆d = 0 ⇒ d = 0` in the corona** `Q(J ⊗ 𝒦)`: a bounded `T` with `T⋆T` compact is compact
(Pedersen, *C⋆-algebras and their automorphism groups*, 1.4; Lance, Ch. 2). -/
theorem stdCorona_eq_zero_of_star_mul_self (d : StdCorona J) (hd : star d * d = 0) : d = 0 := by
  obtain ⟨T, rfl⟩ : ∃ T : StdBdd J, stdCoronaQuot J T = d :=
    ⟨Quotient.out d, (stdCoronaQuot_apply _).trans (Quotient.out_eq' d)⟩
  have h1 : stdCoronaQuot J (star T * T) = stdCoronaQuot J 0 := by
    rw [map_mul (stdCoronaQuot J), map_star (stdCoronaQuot J), map_zero (stdCoronaQuot J)]
    exact hd
  have h2 : CompactEq J (star T * T).1 (0 : StdBdd J).1 := (stdCoronaQuot_eq_iff _ _).mp h1
  have h3 : CompactEq J T.1 (0 : StdBdd J).1 := compactEq_zero_of_star_mul_self T.1 h2
  exact ((stdCoronaQuot_eq_iff T 0).mpr h3).trans (map_zero (stdCoronaQuot J))

end Corona

section Absorb

variable {S : Type} [CStarAlgebra S]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **Absorption from compression domination** (Elliott–Kucerovsky 2001, Thm. 6; Kasparov 1980,
§7; Schafhauser 2020, §5). If every unital `σ : S → 𝓑(H_J)` is a compression `w⋆ ℓ w` of the lift
of `x` by an isometry, then the Busby map of `x` is strongly absorbing for every family `𝒯`. -/
theorem isStronglyAbsorbingBusby_of_isCompressionDominant {x : BusbyCycle S J}
    (hx : x.IsUnital) (hd : x.IsCompressionDominant) (𝒯 : Set (S →⋆ₐ[ℂ] StdBdd J)) :
    IsStronglyAbsorbingBusby (stdCoronaQuot J) (stdCuntzPair J) 𝒯 (x.busby hx) := by
  obtain ⟨T, φ, hφ⟩ := exists_isBusbyAmplification_stdBdd J
  exact isStronglyAbsorbingBusby_of_amplification_compress
    (fun d hd' => stdCorona_eq_zero_of_star_mul_self d hd') (stdCoronaQuot J)
    (stdCuntzPairBdd J) hφ (hd.hdom hx φ 𝒯)

/-- The same statement for a Busby map `θ` given as the class of the lift of `x`. -/
theorem isStronglyAbsorbingBusby_of_isCompressionDominant' {x : BusbyCycle S J}
    (hd : x.IsCompressionDominant) {θ : S →⋆ₐ[ℂ] StdCorona J}
    (hθ : ∀ s, θ s = stdCoronaQuot J (x.bddLift s)) (𝒯 : Set (S →⋆ₐ[ℂ] StdBdd J)) :
    IsStronglyAbsorbingBusby (stdCoronaQuot J) (stdCuntzPair J) 𝒯 θ := by
  obtain ⟨T, φ, hφ⟩ := exists_isBusbyAmplification_stdBdd J
  refine isStronglyAbsorbingBusby_of_amplification_compress
    (fun d hd' => stdCorona_eq_zero_of_star_mul_self d hd') (stdCoronaQuot J)
    (stdCuntzPairBdd J) hφ fun σ _ => ?_
  obtain ⟨w, hw, hc⟩ := hd (φ.comp σ)
  refine ⟨w, hw, fun s => ?_⟩
  rw [hθ s]
  exact (x.isCompressedBy_iff (φ.comp σ) w).mp hc s

end Absorb

end GroupApproximation.Full.TWWSchafhauser

end
