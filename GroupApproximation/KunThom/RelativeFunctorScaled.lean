import GroupApproximation.KunThom.RelativeFunctorBundle

/-!
# The relative cluster functor on a scaled cluster system

On a `ScaledPartialClusterSystem D`, the three numerical families of the relative
cluster functor follow from small relative errors.  Three inputs suffice:
- every bridge has missing mass at most `scale / 100` at its retained object;
- every improvement radius is at most `min scale / 100` on its pair;
- matched objects have scales within the factor `11 / 10`.
The representatives supply the comparability of scales along arrows.

* `scale_comparable_of_rep`: a representative from `X` to `Y` gives
  `10 * scale X ≤ 11 * scale Y` and back.
* `relativeFunctor_respects_of_small`, `relativeFunctor_comp_of_small` and
  `relativeFunctor_faithful_of_small`: the three families.
* `relativeClusterFunctor`: the bundle of Kun–Thom Lemma 4.3 for
  `D.presentation`.  Its inputs are the bridges, the improvement of transported
  representatives, and the small relative errors.
-/

namespace GroupApproximation
namespace ScaledPartialClusterSystem

open FinitePartialBijection GroupoidPresentation

universe u

/-- A representative of the scaled presentation from `X` to `Y` forces the scales
of `X` and `Y` to agree up to the factor `11 / 10`. -/
theorem scale_comparable_of_rep {I : Type u} [Fintype I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L) {X Y : I}
    (f : D.clusterData.Rep X Y) :
    10 * D.scale X ≤ 11 * D.scale Y ∧ 10 * D.scale Y ≤ 11 * D.scale X := by
  have hf := (mem_clusterCandidates (D.act X) (D.act Y) D.h (min (D.scale X) (D.scale Y))
    f.1).mp f.2
  have hf' := hf.symm
  rw [min_comm] at hf'
  exact ⟨D.scale_comparable hf, D.scale_comparable hf'⟩

/-- **Nearness family from small errors.** -/
theorem relativeFunctor_respects_of_small {I : Type u} [Fintype I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L) {R S : Set I}
    (obj : R → S) (β : R → ℕ) (ρ : R → R → ℕ)
    (hβ : ∀ X : R, 100 * β X ≤ D.scale X.1)
    (hρ : ∀ X Y : R, 100 * ρ X Y ≤ min (D.scale X.1) (D.scale Y.1))
    (hobj : ∀ X : R, 10 * D.scale X.1 ≤ 11 * D.scale (obj X).1 ∧
      10 * D.scale (obj X).1 ≤ 11 * D.scale X.1)
    {X Y : R} (f : D.clusterData.Rep X.1 Y.1) :
    2 * ρ X Y + β X + β Y + D.clusterMetric.radius X.1 Y.1 ≤
      8 * D.clusterMetric.radius (obj X).1 (obj Y).1 := by
  show 2 * ρ X Y + β X + β Y + 2 * min (D.scale X.1) (D.scale Y.1) ≤
    8 * (2 * min (D.scale (obj X).1) (D.scale (obj Y).1))
  obtain ⟨hab, hba⟩ := D.scale_comparable_of_rep f
  obtain ⟨hXo, -⟩ := hobj X
  obtain ⟨hYo, -⟩ := hobj Y
  have hβX := hβ X
  have hβY := hβ Y
  have hρXY := hρ X Y
  have hm₁ := min_le_left (D.scale X.1) (D.scale Y.1)
  have hm₂ := min_le_right (D.scale X.1) (D.scale Y.1)
  have hn₁ := min_le_left (D.scale (obj X).1) (D.scale (obj Y).1)
  have hn₂ := min_le_right (D.scale (obj X).1) (D.scale (obj Y).1)
  have hn₃ := min_choice (D.scale (obj X).1) (D.scale (obj Y).1)
  omega

/-- **Composition family from small errors.** -/
theorem relativeFunctor_comp_of_small {I : Type u} [Fintype I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L) {R S : Set I}
    (obj : R → S) (β : R → ℕ) (ρ : R → R → ℕ)
    (hβ : ∀ X : R, 100 * β X ≤ D.scale X.1)
    (hρ : ∀ X Y : R, 100 * ρ X Y ≤ min (D.scale X.1) (D.scale Y.1))
    (hobj : ∀ X : R, 10 * D.scale X.1 ≤ 11 * D.scale (obj X).1 ∧
      10 * D.scale (obj X).1 ≤ 11 * D.scale X.1)
    {X Y Z : R} (f : D.clusterData.Rep X.1 Y.1) (g : D.clusterData.Rep Y.1 Z.1) :
    ρ X Z + ρ X Y + ρ Y Z + 2 * β X + 2 * β Y + 2 * β Z + D.clusterMetric.radius X.1 Z.1 +
      D.clusterMetric.radius X.1 Y.1 + D.clusterMetric.radius Y.1 Z.1 +
        D.clusterMetric.radius (obj X).1 (obj Z).1 ≤
          8 * D.clusterMetric.radius (obj X).1 (obj Z).1 := by
  show ρ X Z + ρ X Y + ρ Y Z + 2 * β X + 2 * β Y + 2 * β Z +
      2 * min (D.scale X.1) (D.scale Z.1) + 2 * min (D.scale X.1) (D.scale Y.1) +
        2 * min (D.scale Y.1) (D.scale Z.1) +
          2 * min (D.scale (obj X).1) (D.scale (obj Z).1) ≤
            8 * (2 * min (D.scale (obj X).1) (D.scale (obj Z).1))
  obtain ⟨hab, hba⟩ := D.scale_comparable_of_rep f
  obtain ⟨hbc, hcb⟩ := D.scale_comparable_of_rep g
  obtain ⟨hXo, -⟩ := hobj X
  obtain ⟨hZo, -⟩ := hobj Z
  have hn₁ := min_le_left (D.scale (obj X).1) (D.scale (obj Z).1)
  have hn₂ := min_le_right (D.scale (obj X).1) (D.scale (obj Z).1)
  have hn₃ := min_choice (D.scale (obj X).1) (D.scale (obj Z).1)
  have hA : 1000 * D.scale X.1 ≤ 1331 * min (D.scale (obj X).1) (D.scale (obj Z).1) := by
    omega
  have hB : 100 * D.scale Y.1 ≤ 121 * min (D.scale (obj X).1) (D.scale (obj Z).1) := by
    omega
  have hC : 1000 * D.scale Z.1 ≤ 1331 * min (D.scale (obj X).1) (D.scale (obj Z).1) := by
    omega
  have hβX := hβ X
  have hβY := hβ Y
  have hβZ := hβ Z
  have hρXZ := hρ X Z
  have hρXY := hρ X Y
  have hρYZ := hρ Y Z
  have hm₁ := min_le_left (D.scale X.1) (D.scale Z.1)
  have hm₂ := min_le_right (D.scale X.1) (D.scale Y.1)
  have hm₃ := min_le_left (D.scale Y.1) (D.scale Z.1)
  omega

/-- **Faithfulness family from small errors.** -/
theorem relativeFunctor_faithful_of_small {I : Type u} [Fintype I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L) {R S : Set I}
    (obj : R → S) (β : R → ℕ) (ρ : R → R → ℕ)
    (hβ : ∀ X : R, 100 * β X ≤ D.scale X.1)
    (hρ : ∀ X Y : R, 100 * ρ X Y ≤ min (D.scale X.1) (D.scale Y.1))
    (hobj : ∀ X : R, 10 * D.scale X.1 ≤ 11 * D.scale (obj X).1 ∧
      10 * D.scale (obj X).1 ≤ 11 * D.scale X.1)
    {X Y : R} (f : D.clusterData.Rep X.1 Y.1) :
    2 * ρ X Y + 5 * β X + 5 * β Y + 2 * D.clusterMetric.radius X.1 Y.1 +
      D.clusterMetric.radius (obj X).1 (obj Y).1 ≤ 8 * D.clusterMetric.radius X.1 Y.1 := by
  show 2 * ρ X Y + 5 * β X + 5 * β Y + 2 * (2 * min (D.scale X.1) (D.scale Y.1)) +
      2 * min (D.scale (obj X).1) (D.scale (obj Y).1) ≤
        8 * (2 * min (D.scale X.1) (D.scale Y.1))
  obtain ⟨hab, hba⟩ := D.scale_comparable_of_rep f
  obtain ⟨-, hoX⟩ := hobj X
  obtain ⟨-, hoY⟩ := hobj Y
  have hβX := hβ X
  have hβY := hβ Y
  have hρXY := hρ X Y
  have hm₁ := min_le_left (D.scale X.1) (D.scale Y.1)
  have hm₂ := min_le_right (D.scale X.1) (D.scale Y.1)
  have hm₃ := min_choice (D.scale X.1) (D.scale Y.1)
  have hn₁ := min_le_left (D.scale (obj X).1) (D.scale (obj Y).1)
  have hn₂ := min_le_right (D.scale (obj X).1) (D.scale (obj Y).1)
  omega

/-- **Kun–Thom, Lemma 4.3, on a scaled cluster system.**  Its inputs are a
matching `π` from `S` onto `R` and bridges from every retained object to its
inverse image.  The transported representatives must improve within `ρ`; the
bridge masses and `ρ` must be at most one hundredth of the scales; and matched
scales must lie within `11 / 10`. -/
noncomputable def relativeClusterFunctor {I : Type u} [Fintype I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L) {R S : Finset I}
    (π : I → I) (hmaps : Set.MapsTo π S R) (hinj : Set.InjOn π S)
    (hsurj : Set.SurjOn π S R)
    (bridge : ∀ X : (R : Set I), FinitePartialBijection (D.model X.1)
      (D.model (ClusterMetric.matchingInverse π hsurj X).1))
    (β : ↥(R : Set I) → ℕ) (ρ : ↥(R : Set I) → ↥(R : Set I) → ℕ)
    (hbridge : ∀ X : (R : Set I), (bridge X).sourceDefect + (bridge X).targetDefect ≤ β X)
    (himprove : ∀ (X Y : (R : Set I)) (b : D.clusterData.Rep X.1 Y.1),
      ∃ r : D.clusterData.Rep (ClusterMetric.matchingInverse π hsurj X).1
          (ClusterMetric.matchingInverse π hsurj Y).1,
        r.1.twoSidedDisagreement (sandwich (bridge X) (bridge Y) b.1) < ρ X Y)
    (hβ : ∀ X : (R : Set I), 100 * β X ≤ D.scale X.1)
    (hρ : ∀ X Y : (R : Set I), 100 * ρ X Y ≤ min (D.scale X.1) (D.scale Y.1))
    (hobj : ∀ X : (R : Set I),
      10 * D.scale X.1 ≤ 11 * D.scale (ClusterMetric.matchingInverse π hsurj X).1 ∧
        10 * D.scale (ClusterMetric.matchingInverse π hsurj X).1 ≤ 11 * D.scale X.1) :
    D.presentation.RelativeClusterFunctor R S :=
  ClusterMetric.relativeClusterFunctor D.clusterMetric π hmaps hinj hsurj bridge β ρ hbridge
    himprove
    (fun {X Y} f ↦ relativeFunctor_respects_of_small D (ClusterMetric.matchingInverse π hsurj)
      β ρ hβ hρ hobj (X := X) (Y := Y) f)
    (fun {X Y Z} f g ↦ relativeFunctor_comp_of_small D (ClusterMetric.matchingInverse π hsurj)
      β ρ hβ hρ hobj (X := X) (Y := Y) (Z := Z) f g)
    (fun {X Y} f ↦ relativeFunctor_faithful_of_small D (ClusterMetric.matchingInverse π hsurj)
      β ρ hβ hρ hobj (X := X) (Y := Y) f)

end ScaledPartialClusterSystem
end GroupApproximation
