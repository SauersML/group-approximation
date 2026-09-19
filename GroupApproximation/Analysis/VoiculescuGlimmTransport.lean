import GroupApproximation.Analysis.VoiculescuGlimmReflection

/-!
# (V2) Positivity on the Calkin side, in the order the extension will use

`Analysis/VoiculescuGlimmReflection` reflected positivity through the essential
map in an order-free form: `(π a)⁻ = 0` gives `0 ≤ a`.  The state transport
needs it in the form the extension theorem consumes, `0 ≤ π a → 0 ≤ a`, and
that is the one place where an order on `Q(H)` has to exist.  This module is
where it is introduced, and it is introduced exactly once.

## The instance situation

`Q(H)` is a general C\*-algebra, so Mathlib registers no order for it; the tree's
convention (`Analysis/DoubledData`) is that the consumer supplies
`CStarAlgebra.spectralOrder`.  Layered on top of that is the continuous
functional calculus, whose derivation on a quotient is too deep for open
instance search — `NegPart (CalkinQuotient H)` times out at the default budget.
The ladder below is the pattern that works, copied verbatim from
`Analysis/VoiculescuGlimmReflection`: three `local instance` rungs, each a named
Mathlib *theorem* applied in tactic mode with the carrier pinned by `(A := …)`,
and no local `CStarAlgebra` — the global instance must stay the only copy, since
a second one turns every downstream predicate into a `Star`/`Ring` diamond.

`local` means the ladder does not travel through an import, so each module on
this surface carries its own copy.  `[Nontrivial H]` is part of it: the
quotient's C\*-instance wants `Nontrivial (H →L[ℂ] H)`, and its absence shows up
as a synthesis failure that never mentions nontriviality.

## What is proved

That the restriction of the quotient map to `A` is injective (this is
`A ∩ K(H) = 0`, restated), that self-adjointness reflects along it, and hence
that positivity does.  The last is the hypothesis `StateExtension` asks of the
functional transported to the image, and with it the remaining assembly —
extend, pull back — is plumbing.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace
open scoped ComplexOrder

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Nontrivial H]

noncomputable local instance :
    ContinuousFunctionalCalculus ℂ (CalkinAlgebra.CalkinQuotient H)
      IsStarNormal := by
  exact IsStarNormal.instContinuousFunctionalCalculus (A := CalkinAlgebra.CalkinQuotient H)

noncomputable local instance :
    NonUnitalContinuousFunctionalCalculus ℂ (CalkinAlgebra.CalkinQuotient H)
      IsStarNormal := by
  exact ContinuousFunctionalCalculus.toNonUnital (A := CalkinAlgebra.CalkinQuotient H)

noncomputable local instance :
    NonUnitalContinuousFunctionalCalculus ℝ (CalkinAlgebra.CalkinQuotient H)
      IsSelfAdjoint := by
  exact IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
    (A := CalkinAlgebra.CalkinQuotient H)

noncomputable local instance :
    PartialOrder (CalkinAlgebra.CalkinQuotient H) :=
  CStarAlgebra.spectralOrder (CalkinAlgebra.CalkinQuotient H)

noncomputable local instance :
    StarOrderedRing (CalkinAlgebra.CalkinQuotient H) :=
  CStarAlgebra.spectralOrderedRing (CalkinAlgebra.CalkinQuotient H)

omit [Nontrivial H] in
/-- **The essential map restricted to a subalgebra.** -/
def essentialRestrict (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    ↥A →⋆ₐ[ℂ] CalkinAlgebra.CalkinQuotient H :=
  (CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H)).comp A.subtype

omit [Nontrivial H] in
theorem essentialRestrict_apply (A : StarSubalgebra ℂ (H →L[ℂ] H)) (a : ↥A) :
    essentialRestrict A a
      = CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H) (a : H →L[ℂ] H) :=
  rfl

omit [Nontrivial H] in
/-- **`A ∩ K(H) = 0`, restated as injectivity.**  This is the only use of the
hypothesis in the transport, and it is what makes the transported functional
well defined. -/
theorem injective_essentialRestrict {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hAK : ∀ T ∈ A, IsCompactOperator T → T = 0) :
    Function.Injective (essentialRestrict A) := by
  intro a b hab
  have h0 : essentialRestrict A (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  rw [essentialRestrict_apply, CStarTensor.quotientStarMk_apply] at h0
  have hmem : ((a : H →L[ℂ] H) - (b : H →L[ℂ] H)) ∈ CalkinAlgebra.compactIdeal H :=
    Ideal.Quotient.eq_zero_iff_mem.mp h0
  have hz : (a : H →L[ℂ] H) - (b : H →L[ℂ] H) = 0 :=
    hAK _ (A.sub_mem a.2 b.2) ((CalkinAlgebra.mem_compactIdeal H).mp hmem)
  exact Subtype.ext (sub_eq_zero.mp hz)

omit [Nontrivial H] in
/-- **Self-adjointness reflects.**  A `⋆`-homomorphism carries the involution,
so an injective one reflects it. -/
theorem isSelfAdjoint_of_essential {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hAK : ∀ T ∈ A, IsCompactOperator T → T = 0) {a : ↥A}
    (h : IsSelfAdjoint (essentialRestrict A a)) : IsSelfAdjoint (a : H →L[ℂ] H) := by
  have hstar : essentialRestrict A (star a) = essentialRestrict A a := by
    rw [map_star, h.star_eq]
  have := injective_essentialRestrict hAK hstar
  exact congrArg (fun z : ↥A ↦ (z : H →L[ℂ] H)) this

/-- **Positivity reflects, in the form the extension consumes.**  A positive
element of the image comes from a positive element of `A` — which is what makes
the transported functional positive against `Q(H)`'s positives, and hence
extendable.

The negative part is the mechanism: `0 ≤ π a` says `(π a)⁻ = 0`, and
`Analysis/VoiculescuGlimmReflection` turns that into `0 ≤ a` without ever
mentioning the quotient's order again. -/
theorem nonneg_of_essential_nonneg {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hA : IsClosed (A : Set (H →L[ℂ] H)))
    (hAK : ∀ T ∈ A, IsCompactOperator T → T = 0) {a : ↥A}
    (hpos : 0 ≤ essentialRestrict A a) : 0 ≤ (a : H →L[ℂ] H) := by
  have hsa' : IsSelfAdjoint (essentialRestrict A a) := hpos.isSelfAdjoint
  have hsa : IsSelfAdjoint (a : H →L[ℂ] H) := isSelfAdjoint_of_essential hAK hsa'
  have hzero : (CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H)
      (a : H →L[ℂ] H))⁻ = 0 := by
    rw [← essentialRestrict_apply]
    exact (CFC.negPart_eq_zero_iff (essentialRestrict A a) hsa').mpr hpos
  exact nonneg_of_essential_negPart_eq_zero hA hAK a.2 hsa hzero

end

end ShulmanFill
end GroupApproximation
