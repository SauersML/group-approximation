import GroupApproximation.Higman.HNNStableHull
import GroupApproximation.Higman.OmegaHalfLineReduction

/-!
# An asymmetric HNN criterion for a one-sided Omega construction

The two-sided modified Omega tower fails because its outer edge is an
automorphism of the whole embedded `F₃`: both stable-letter signs can always
pinch, so a legal right insertion also produces the illegal left insertion.

For a replacement, the edge must be genuinely asymmetric.  The target edge
subgroup acts as a gate: a negative stable-letter pinch is possible only for
elements which lie in that target.  `OneSidedGate` records exactly the three
facts needed after the arithmetic construction of that target:

* the seed lies in the proposed one-sided answer;
* a forward pinch stays in the answer;
* a reverse pinch is safe whenever the target gate permits it.

Britton's lemma, through `HNNDescent.stableHull_eq_generatedBase`, then says
that no word with an uncancelled stable-letter sign can return to the base.
The final theorem packages the exact subgroup intersection required by a
benign witness.  It is intended to be instantiated twice, for `omegaGE` and
`omegaLT`, and then combined by `omegaInput_of_halfLine`.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open HNNExtension

variable {P : Type} [Group P] {A B : Subgroup P}

/-- Arithmetic data certifying that the proposed answer contains every base
element created by either legal orientation of an asymmetric HNN pinch. -/
structure OneSidedGate (φ : A ≃* B) (Z Y : Subgroup P) : Prop where
  seed : Z ≤ Y
  forward : ∀ a : A, (a : P) ∈ Y → (φ a : P) ∈ Y
  backward : ∀ b : B, (b : P) ∈ Y → (φ.symm b : P) ∈ Y

theorem OneSidedGate.stable {φ : A ≃* B} {Z Y : Subgroup P}
    (h : OneSidedGate φ Z Y) : HNNDescent.Stable φ Y :=
  ⟨h.forward, h.backward⟩

/-- The part of `⟨Z,t⟩` which returns to the HNN base lies in `Y`.  Reduced
words with a surviving stable-letter sign are excluded by Britton's lemma;
the only reductions left are the two gate clauses. -/
theorem generatedBase_le_of_oneSidedGate (φ : A ≃* B) {Z Y : Subgroup P}
    (h : OneSidedGate φ Z Y) : HNNDescent.generatedBase φ Z ≤ Y := by
  rw [← HNNDescent.stableHull_eq_generatedBase]
  exact HNNDescent.stableHull_le φ h.seed h.stable

variable {F : Type} [Group F]

/-- Pull the base-return bound back to the distinguished source group. -/
theorem generatedSource_le_of_oneSidedGate (φ : A ≃* B) {Z Y : Subgroup P}
    (h : OneSidedGate φ Z Y) (emb : F →* P) {H : Subgroup F}
    (hcut : Y.comap emb ≤ H) :
    (Subgroup.closure (HNNDescent.genSet φ Z)).comap
        ((HNNExtension.of : P →* HNNExtension P A B φ).comp emb) ≤ H := by
  intro x hx
  apply hcut
  exact generatedBase_le_of_oneSidedGate φ h hx

/-- **Exact one-sided cutter.**  If source elements of `H` already occur in
the seed, and the proposed base answer cuts back to at most `H`, then the
asymmetric HNN subgroup cuts out exactly `H`. -/
theorem generatedSource_eq_of_oneSidedGate (φ : A ≃* B) {Z Y : Subgroup P}
    (h : OneSidedGate φ Z Y) (emb : F →* P) {H : Subgroup F}
    (hseed : H ≤ Z.comap emb) (hcut : Y.comap emb ≤ H) :
    (Subgroup.closure (HNNDescent.genSet φ Z)).comap
        ((HNNExtension.of : P →* HNNExtension P A B φ).comp emb) = H := by
  apply le_antisymm
  · exact generatedSource_le_of_oneSidedGate φ h emb hcut
  · intro x hx
    change HNNExtension.of (emb x) ∈
      Subgroup.closure (HNNDescent.genSet φ Z)
    exact Subgroup.subset_closure (Or.inl ⟨emb x, hseed hx, rfl⟩)

end Omega
end Higman
end GroupApproximation
