import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplitExtBusby

/-!
# Compression domination of a Busby cycle

Lane `TWWSch3c2C3`, work order `WO-TWWSch-3c2-C3`, first part. Sources: G. A. Elliott and
D. Kucerovsky, Pacific J. Math. 198 (2001), proof of Thm. 6; G. G. Kasparov, J. Operator Theory 4
(1980), §7; C. Schafhauser, J. reine angew. Math. 759 (2020), §5. Manuscript label:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (the absorption step).

Let `x : BusbyCycle S J` be a cycle with bounded lift `ℓ = x.bddLift`. The analytic core of the
Elliott–Kucerovsky theorem produces, for every unital `⋆`-homomorphism `σ : S → 𝓑(H_J)`, an
isometry `w` of `H_J` with `w⋆ ℓ(s) w ≡ σ(s)` modulo compacts. This file fixes that vocabulary
and does the algebra that turns it into the hypothesis `hdom` of `ExtensionAbsorbRepeat`:

* `BusbyCycle.IsCompressedBy x σ w`: `w⋆ ℓ(s) w − σ(s)` is compact for every `s`;
* `BusbyCycle.IsCompressionDominant x`: every unital `σ` is such a compression by an isometry;
* `BusbyCycle.isCompressedBy_iff`: the corona form
  `π(w)⋆ π(ℓ(s)) π(w) = π(σ(s))`, with `π = stdCoronaQuot J`;
* `BusbyCycle.IsCompressedBy.of_compactEq`: compressions only depend on `w` modulo compacts, so an
  exact isometry may replace a compact perturbation of a near isometry (`IsStdNearIsometry`);
* `BusbyCycle.busby_compress_of_isCompressedBy`: the same with the Busby map `x.busby hx`;
* `BusbyCycle.IsCompressionDominant.hdom`: for any `⋆`-endomorphism `φ` of `𝓑(H_J)` (the
  amplification), the domination hypothesis of `isStronglyAbsorbingBusby_of_amplification_compress`.

A unital `⋆`-homomorphism is the same as a `StarAlgHom` out of a unital algebra (`map_one`), so no
separate unitality hypothesis on `σ` appears.
-/

noncomputable section

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

section NearIsometry

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- `w` is a **near isometry** of `H_J`: `w⋆w − 1` is compact and has operator bound `c < 1`.
The polar correction `w (w⋆w)^{-1/2}` of such a `w` is an isometry differing from `w` by a compact
(Elliott–Kucerovsky 2001, proof of Thm. 6). -/
def IsStdNearIsometry (w : StdBdd J) : Prop :=
  CompactEq J (star w * w).1 (1 : StdBdd J).1 ∧
    ∃ c : ℝ, c < 1 ∧ Adjointable.IsBoundedBy (star w * w - 1 : StdBdd J).1 c

end NearIsometry

section Compress

variable {S : Type} [CStarAlgebra S]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- `w` **compresses** the cycle `x` onto `σ`: `w⋆ ℓ(s) w ≡ σ(s)` modulo compacts, for every `s`
(Elliott–Kucerovsky 2001, Thm. 6). -/
def BusbyCycle.IsCompressedBy (x : BusbyCycle S J) (σ : S →⋆ₐ[ℂ] StdBdd J) (w : StdBdd J) :
    Prop :=
  ∀ s : S, CompactEq J (star w * x.bddLift s * w).1 (σ s).1

/-- `x` **dominates by compression** every unital `⋆`-homomorphism `σ : S → 𝓑(H_J)`: some
isometry `w` compresses `x` onto `σ` (Elliott–Kucerovsky 2001, Thm. 6; Schafhauser 2020, §5). -/
def BusbyCycle.IsCompressionDominant (x : BusbyCycle S J) : Prop :=
  ∀ σ : S →⋆ₐ[ℂ] StdBdd J, ∃ w : StdBdd J, star w * w = 1 ∧ x.IsCompressedBy σ w

/-- The corona value of a compression. -/
theorem stdCoronaQuot_compress (w T : StdBdd J) :
    stdCoronaQuot J (star w * T * w) =
      star (stdCoronaQuot J w) * stdCoronaQuot J T * stdCoronaQuot J w := by
  rw [map_mul (stdCoronaQuot J), map_mul (stdCoronaQuot J), map_star (stdCoronaQuot J)]

/-- **Corona form of a compression**: `π(w)⋆ π(ℓ(s)) π(w) = π(σ(s))` for every `s`. -/
theorem BusbyCycle.isCompressedBy_iff (x : BusbyCycle S J) (σ : S →⋆ₐ[ℂ] StdBdd J)
    (w : StdBdd J) :
    x.IsCompressedBy σ w ↔ ∀ s : S, star (stdCoronaQuot J w) * stdCoronaQuot J (x.bddLift s) *
      stdCoronaQuot J w = stdCoronaQuot J (σ s) := by
  unfold BusbyCycle.IsCompressedBy
  refine forall_congr' fun s => ?_
  rw [← stdCoronaQuot_compress w (x.bddLift s)]
  exact (stdCoronaQuot_eq_iff (star w * x.bddLift s * w) (σ s)).symm

/-- A compression only depends on `w` modulo compacts. -/
theorem BusbyCycle.IsCompressedBy.of_compactEq {x : BusbyCycle S J} {σ : S →⋆ₐ[ℂ] StdBdd J}
    {w w' : StdBdd J} (h : x.IsCompressedBy σ w) (hw : CompactEq J w'.1 w.1) :
    x.IsCompressedBy σ w' := by
  have e : stdCoronaQuot J w' = stdCoronaQuot J w := (stdCoronaQuot_eq_iff w' w).mpr hw
  refine (x.isCompressedBy_iff σ w').mpr fun s => ?_
  rw [e]
  exact (x.isCompressedBy_iff σ w).mp h s

/-- An isometry compact-close to a compressing element compresses too: this is how an exact
isometry replaces a near isometry (`IsStdNearIsometry`). -/
theorem BusbyCycle.isCompressionDominant_of_compactEq (x : BusbyCycle S J)
    (h : ∀ σ : S →⋆ₐ[ℂ] StdBdd J, ∃ w w' : StdBdd J, x.IsCompressedBy σ w ∧
      star w' * w' = 1 ∧ CompactEq J w'.1 w.1) :
    x.IsCompressionDominant := by
  intro σ
  obtain ⟨w, w', hc, hw', hww'⟩ := h σ
  exact ⟨w', hw', hc.of_compactEq hww'⟩

/-- **Compression through the Busby map**: `π(w)⋆ (x.busby hx)(s) π(w) = π(σ(s))`. -/
theorem BusbyCycle.busby_compress_of_isCompressedBy {x : BusbyCycle S J} (hx : x.IsUnital)
    {σ : S →⋆ₐ[ℂ] StdBdd J} {w : StdBdd J} (h : x.IsCompressedBy σ w) (s : S) :
    star (stdCoronaQuot J w) * x.busby hx s * stdCoronaQuot J w = stdCoronaQuot J (σ s) := by
  rw [BusbyCycle.busby_apply_eq_quot]
  exact (x.isCompressedBy_iff σ w).mp h s

/-- **Domination hypothesis for the amplification theorem** (Elliott–Kucerovsky 2001, Thm. 6):
if `x` dominates by compression, then for every `⋆`-endomorphism `φ` of `𝓑(H_J)` and every
`σ ∈ 𝒯`, some isometry `w` satisfies `π(w)⋆ (x.busby hx)(s) π(w) = π(φ(σ(s)))`. This is the
`hdom` of `isStronglyAbsorbingBusby_of_amplification_compress` (`ExtensionAbsorbRepeat`). -/
theorem BusbyCycle.IsCompressionDominant.hdom {x : BusbyCycle S J}
    (hd : x.IsCompressionDominant) (hx : x.IsUnital) (φ : StdBdd J →⋆ₐ[ℂ] StdBdd J)
    (𝒯 : Set (S →⋆ₐ[ℂ] StdBdd J)) :
    ∀ σ ∈ 𝒯, ∃ w : StdBdd J, star w * w = 1 ∧ ∀ s : S,
      star (stdCoronaQuot J w) * x.busby hx s * stdCoronaQuot J w =
        stdCoronaQuot J (φ (σ s)) := by
  intro σ _
  obtain ⟨w, hw, hc⟩ := hd (φ.comp σ)
  exact ⟨w, hw, fun s => BusbyCycle.busby_compress_of_isCompressedBy hx hc s⟩

end Compress

end GroupApproximation.Full.TWWSchafhauser

end
