import GroupApproximation.Sofic.GreendlingerDeepInvariant

/-!
# The sharp gate along the drop route

`GreendlingerSharpTwins.sharpGreendlingerGate_of_cascadeLandingSharp` assembles
the sharp Greendlinger gate from a `CascadeLandingSharp` family, and
`GreendlingerSharpResidualWiring` feeds that from `SharpResiduals`, whose two
fields are `DeepOverrunArcSharp` and `LandingProductionBetaSharp'`.

There is a second route, and it is shorter.  `GreendlingerDeepInvariant`
carries the *drop* form of the invariant, in which the arc is read at position
`0` and the offset conjunct disappears; every link of it is already twinned:

```
DeepWindowDropSharp
  → DeepArcDropSharp             (deepArcDropSharp_of_deepWindowDropSharp)
  + LandingProductionSharp
  → CascadeLandingDropSharp      (cascadeLandingDropSharp_of_deepArcDropSharp_of_landingSharp)
  → GreendlingerConclusionSharp  (greendlingerConclusionSharp_of_cascadeLandingDropSharp)
```

and `GreendlingerFreeGate.SharpGreendlingerGate` is *literally* a family of
`GreendlingerConclusionSharp`.  So the gate follows from two families, and this
file performs that assembly.

## Why this route is worth stating separately

Both open leaves are milder than the ones `SharpResiduals` asks for.

* `DeepWindowDropSharp` has no offset field.  The located predicates carry
  `M.length + j - (c.length + t.length) ≤ A.length`, denominated in the *head*
  rotation while the arc is cut from the *landing* one; the drop form reads the
  arc at `0` and never incurs it.  `GreendlingerDeepTailWindow` says outright
  that the located conjunct is unpayable once `|t| > 2·|t₃|` and that the field
  "can only be deleted below the invariant redesign" --- which is this route.
* `LandingProductionSharp` is the plain landing family, not the disjunctive
  `LandingProductionBetaSharp'` that the residual bundle takes.

## What is proved here

Only the assembly.  Both families are hypotheses and neither is discharged;
their `λ`-free counterparts are open too.  The side conditions the gate does
not supply --- `0 < lam` and `∀ r ∈ R, r ≠ []` --- are recovered exactly as the
`CascadeLandingSharp` assembly recovers them, from a piece of the empty word,
and the all-relators-empty case is refuted through the trivial normal closure.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The gate from the drop-form invariant -/

/-- **The sharp gate, from a `CascadeLandingDropSharp` family.**

The drop-form counterpart of
`GreendlingerSharpTwins.sharpGreendlingerGate_of_cascadeLandingSharp`, and the
same two-case assembly: where some relator is nonempty the two side conditions
are recovered from the empty piece, and where every relator is empty the
normal closure is trivial and no reduced nonempty word lies in it. -/
theorem sharpGreendlingerGate_of_cascadeLandingDropSharp [DecidableEq α]
    (hland : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → CascadeLandingDropSharp R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate α := by
  intro R lam hcyc hlam hmetric
  by_cases hex : ∃ r ∈ R, r ≠ []
  · obtain ⟨s₁, hs₁, s₂, hs₂, hne⟩ := exists_two_distinct_symmetrization hcyc hex
    obtain ⟨r, hr, hrne⟩ := hex
    have hlam0 : 0 < lam :=
      lam_pos_of_metric hmetric hs₁ hs₂ hne (subset_symmetrization R hr) hrne
    have hRne : ∀ q ∈ R, q ≠ [] := fun q hq =>
      ne_nil_of_metric_lam hmetric hs₁ hs₂ hne (subset_symmetrization R hq)
    exact greendlingerConclusionSharp_of_cascadeLandingDropSharp hcyc hRne hlam0
      hlam (hland R lam hcyc hRne hlam0 hlam hmetric)
  · intro w hw hwne hmem
    exfalso
    push Not at hex
    have hsub : FreeGroup.mk '' R ⊆
        ((⊥ : Subgroup (FreeGroup α)) : Set (FreeGroup α)) := by
      rintro _ ⟨r, hr, rfl⟩
      have hone : FreeGroup.mk r = (1 : FreeGroup α) := by
        rw [hex r hr, ← FreeGroup.one_eq_mk]
      simp [hone]
    have hb := Subgroup.normalClosure_le_normal hsub hmem
    rw [Subgroup.mem_bot] at hb
    have h1 : FreeGroup.mk w = FreeGroup.mk ([] : List (α × Bool)) := by
      rw [hb]
      exact FreeGroup.one_eq_mk
    have h2 := FreeGroup.reduce.sound h1
    rw [hw.reduce_eq, FreeGroup.IsReduced.nil.reduce_eq] at h2
    exact hwne h2

/-! ## 2.  The gate from the two drop-route leaves -/

/-- **The sharp gate from a window family and a landing family.**

This is the shortest statement of what the routing lane still needs.  Supply

* a `DeepWindowDropSharp` family --- where two cancellations leave a window
  longer than `(1 - 3λ)` of its rotation, with the arc read at position `0`;
* a `LandingProductionSharp` family;

and the sharp Greendlinger gate follows, hence torsion-freeness of the
presented quotient, hence the router.

Both arguments are hypotheses.  Nothing here discharges either. -/
theorem sharpGreendlingerGate_of_windowDropSharp_of_landingSharp [DecidableEq α]
    (hwin : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepWindowDropSharp R lam)
    (hland : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → LandingProductionSharp R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate α :=
  sharpGreendlingerGate_of_cascadeLandingDropSharp
    fun R lam hcyc hRne hlam0 hlam hmetric =>
      cascadeLandingDropSharp_of_deepArcDropSharp_of_landingSharp
        (deepArcDropSharp_of_deepWindowDropSharp
          (hwin R lam hcyc hRne hlam0 hlam hmetric))
        (hland R lam hcyc hRne hlam0 hlam hmetric)

/-- The drop-route gate on the router's own alphabet, which is the instance
every construction in this repository consumes. -/
theorem sharpGreendlingerGate_fin_two_of_windowDropSharp_of_landingSharp
    (hwin : ∀ (R : Set (List (Fin 2 × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepWindowDropSharp R lam)
    (hland : ∀ (R : Set (List (Fin 2 × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → LandingProductionSharp R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate (Fin 2) :=
  sharpGreendlingerGate_of_windowDropSharp_of_landingSharp hwin hland

end SmallCancellationRouter
end GroupApproximation
