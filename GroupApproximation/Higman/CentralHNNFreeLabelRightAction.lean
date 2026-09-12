import GroupApproximation.Higman.CentralHNNFreeLabelKernel

/-!
# Right action on central-HNN free labels

Conjugating a stable conjugate by a base element right-translates its chosen
right-coset label.  The translation is injective, hence it cannot create free
word cancellation.  This is the generic normal-form mechanism used by the
order-sensitive Omega scan.
-/

namespace GroupApproximation
namespace Higman
namespace CentralHNNFreeLabel

open HNNExtension

variable {G : Type} [Group G] {M : Subgroup G}

noncomputable def rightLabel
    (d : HNNExtension.NormalWord.TransversalPair G M M) (g : G)
    (q : Label M d) : Label M d :=
  ((d.compl (1 : ℤˣ)).equiv ((q : G) * g)).2

theorem rightLabel_injective
    (d : HNNExtension.NormalWord.TransversalPair G M M) (g : G) :
    Function.Injective (rightLabel (M := M) d g) := by
  intro q r hqr
  have hcoset : RightCosetEquivalence (M : Set G)
      ((q : G) * g) ((r : G) * g) := by
    exact ((d.compl (1 : ℤˣ)).equiv_snd_eq_iff_rightCosetEquivalence).mp hqr
  have hcoset' : RightCosetEquivalence (M : Set G) (q : G) (r : G) := by
    rw [RightCosetEquivalence, rightCoset_eq_iff] at hcoset ⊢
    simpa [mul_inv_rev, mul_assoc] using hcoset
  have hlabels :=
    ((d.compl (1 : ℤˣ)).equiv_snd_eq_iff_rightCosetEquivalence).mpr hcoset'
  simpa only [label_self] using hlabels

/-- Right translation of labels is exactly conjugation of stable conjugates
by the corresponding base element. -/
theorem stableConj_rightLabel
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (g : G) (q : Label M d) :
    of g⁻¹ * stableConj M d q * of g =
      stableConj M d (rightLabel (M := M) d g q) := by
  rw [stableConj_eq_conj_of_label_eq M d (rightLabel (M := M) d g q)
    ((q : G) * g) rfl]
  unfold stableConj
  simp only [map_mul, map_inv]
  group

/-- The same right translation on an arbitrary free word of stable
conjugates. -/
theorem stableConjLift_rightLabel
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (g : G) (w : FreeGroup (Label M d)) :
    of g⁻¹ * stableConjLift M d w * of g =
      stableConjLift M d (FreeGroup.map (rightLabel (M := M) d g) w) := by
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of q =>
      simp only [stableConjLift, FreeGroup.lift_apply_of,
        FreeGroup.map.of]
      exact stableConj_rightLabel (M := M) d g q
  | mul x y hx hy =>
      rw [map_mul (stableConjLift M d) x y]
      calc
        of g⁻¹ * (stableConjLift M d x * stableConjLift M d y) * of g =
            (of g⁻¹ * stableConjLift M d x * of g) *
              (of g⁻¹ * stableConjLift M d y * of g) := by
                rw [map_inv]
                group
        _ = stableConjLift M d (FreeGroup.map (rightLabel (M := M) d g) x) *
              stableConjLift M d (FreeGroup.map (rightLabel (M := M) d g) y) := by
                rw [hx, hy]
        _ = stableConjLift M d
              (FreeGroup.map (rightLabel (M := M) d g) (x * y)) := by
                rw [map_mul (FreeGroup.map (rightLabel (M := M) d g))]
                exact (map_mul (stableConjLift M d) _ _).symm
  | inv_of q hq =>
      simp only [stableConjLift, FreeGroup.lift_apply_of,
        map_inv, FreeGroup.map.of]
      calc
        of g⁻¹ * (stableConj M d q)⁻¹ * of g =
            (of g⁻¹ * stableConj M d q * of g)⁻¹ := by
              rw [map_inv]
              group
        _ = (stableConj M d (rightLabel (M := M) d g q))⁻¹ := by
          rw [stableConj_rightLabel (M := M) d g q]

theorem freeGroupMap_rightLabel_injective
    (d : HNNExtension.NormalWord.TransversalPair G M M) (g : G) :
    Function.Injective (FreeGroup.map (rightLabel (M := M) d g)) :=
  FreeGroup.map_injective (rightLabel_injective (M := M) d g)

end CentralHNNFreeLabel
end Higman
end GroupApproximation
