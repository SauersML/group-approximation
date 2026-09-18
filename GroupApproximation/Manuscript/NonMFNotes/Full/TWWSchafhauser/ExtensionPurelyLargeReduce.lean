import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionPurelyLargeChain

/-!
# Purely large separable subextensions

Lane TWWSch3c3, work order WO-TWWSch-3c-3 (C. Schafhauser, *Subalgebras of simple
AF-algebras*, Ann. of Math. 192 (2020), §3--4; *A new proof of the Tikuisis--White--Winter
theorem*, J. reine angew. Math. 759 (2020), §4; non_mf_group_notes.tex,
thm:fixed-radical-membership).

This file gives the Löwenheim--Skolem closure.  Let `P` be separably inheritable (for
example the K-theoretic conditions, combined with `IsSeparablyInheritable.and`) and let
`J` carry uniform purely-large witnesses.  Then every separable closed `D₀` lies in a
separable closed `D` with `P D` for which the pulled-back extension
`0 → D ∩ J → D → D/(D ∩ J) → 0` is purely large.  The versions below contain either a
countable set or the range of a continuous map from a separable space, for example a
ucp lift of `θ : S → Q^ω`.

* `exists_isSepClosed_and_isPurelyLargeIdeal`;
* `isPurelyLargeExtension_sepIdeal`;
* `exists_separable_purelyLarge`, `exists_separable_purelyLarge_range`.

Nothing here has been compiled (lane rule).
-/

namespace GroupApproximation.Full.TWWSchafhauser

noncomputable section

open TopologicalSpace

variable {B : Type} [CStarAlgebra B] {J : NonUnitalStarSubalgebra ℂ B}

/-- **Löwenheim--Skolem closure.**  Interleave the enlargements given by `P` with the
countable purely-large witness steps. -/
theorem exists_isSepClosed_and_isPurelyLargeIdeal {P : StarSubalgebra ℂ B → Prop}
    (hP : IsSeparablyInheritable P) (W : PurelyLargeWitnessData J)
    (hJR : ∀ b x : B, x ∈ J → x * b ∈ J) (D₀ : StarSubalgebra ℂ B) (h₀ : IsSepClosed D₀) :
    ∃ D : StarSubalgebra ℂ B, D₀ ≤ D ∧ IsSepClosed D ∧ P D ∧ IsPurelyLargeIdeal D J := by
  have hnext : ∀ E : {D : StarSubalgebra ℂ B // IsSepClosed D},
      ∃ F : {D : StarSubalgebra ℂ B // IsSepClosed D},
        E.1 ≤ F.1 ∧ purelyLargeStep W E.1 F.1 ∧ P F.1 := by
    intro E
    obtain ⟨s, hs, hsD⟩ := purelyLargeStep_exists W E.1 E.2
    obtain ⟨F₁, hEF₁, hsF₁, hF₁⟩ := exists_isSepClosed_le_of_countable E.2 hs
    obtain ⟨F, hF₁F, hF, hPF⟩ := hP.1 F₁ hF₁
    exact ⟨⟨F, hF⟩, hEF₁.trans hF₁F,
      hsD F (hEF₁.trans hF₁F) (Set.Subset.trans hsF₁ (SetLike.coe_subset_coe.mpr hF₁F)), hPF⟩
  choose next hle hst hPn using hnext
  obtain ⟨a, ha0, ha⟩ : ∃ a : ℕ → {D : StarSubalgebra ℂ B // IsSepClosed D},
      a 0 = next ⟨D₀, h₀⟩ ∧ ∀ n, a (n + 1) = next (a n) :=
    ⟨fun n => Nat.rec (motive := fun _ => {D : StarSubalgebra ℂ B // IsSepClosed D})
      (next ⟨D₀, h₀⟩) (fun _ E => next E) n, rfl, fun _ => rfl⟩
  have hsucc : ∀ n, (a n).1 ≤ (a (n + 1)).1 := by
    intro n
    rw [ha n]
    exact hle _
  have hmono : Monotone fun n => (a n).1 := monotone_nat_of_le_succ hsucc
  have hsteps : ∀ n, purelyLargeStep W (a n).1 (a (n + 1)).1 := by
    intro n
    rw [ha n]
    exact hst _
  have hPa : ∀ n, P (a n).1 := by
    intro n
    cases n with
    | zero =>
      rw [ha0]
      exact hPn _
    | succ n =>
      rw [ha n]
      exact hPn _
  have h0 : D₀ ≤ (a 0).1 := by
    rw [ha0]
    exact hle _
  exact ⟨chainClosure fun n => (a n).1, h0.trans (le_chainClosure (fun n => (a n).1) 0),
    isSepClosed_chainClosure hmono fun n => (a n).2, hP.2 _ hmono (fun n => (a n).2) hPa,
    isPurelyLargeIdeal_chainClosure_of_step W hmono (fun n => (a n).2) hJR hsteps⟩

/-- A purely large ideal gives a purely large extension `0 → D ∩ J → D → D/(D ∩ J) → 0`. -/
theorem isPurelyLargeExtension_sepIdeal {D : StarSubalgebra ℂ B}
    (h : IsPurelyLargeIdeal D J) : IsPurelyLargeExtension D (sepIdeal D J) := by
  have hss : sepIdeal D (sepIdeal D J) = sepIdeal D J := by
    ext x
    exact ⟨fun hx => (mem_sepIdeal.mp hx).2,
      fun hx => mem_sepIdeal.mpr ⟨(mem_sepIdeal.mp hx).1, hx⟩⟩
  refine ⟨fun x hx => SetLike.mem_coe.mpr (mem_sepIdeal.mp (SetLike.mem_coe.mp hx)).1, ?_⟩
  intro e he heI
  rw [hss]
  exact h e he fun heJ => heI (mem_sepIdeal.mpr ⟨he, heJ⟩)

/-- **Separable purely large subextension containing a countable set.** -/
theorem exists_separable_purelyLarge {P : StarSubalgebra ℂ B → Prop}
    (hP : IsSeparablyInheritable P) (W : PurelyLargeWitnessData J)
    (hJR : ∀ b x : B, x ∈ J → x * b ∈ J) {s : Set B} (hs : s.Countable) :
    ∃ D : StarSubalgebra ℂ B, s ⊆ D ∧ IsSepClosed D ∧ P D ∧
      IsPurelyLargeExtension D (sepIdeal D J) := by
  obtain ⟨D, hD₀, hD, hPD, hPL⟩ :=
    exists_isSepClosed_and_isPurelyLargeIdeal hP W hJR _ (isSepClosed_adjoinClosure hs)
  refine ⟨D, fun x hx => hD₀ ?_, hD, hPD, isPurelyLargeExtension_sepIdeal hPL⟩
  exact StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ s hx)

/-- **Separable purely large subextension containing the range of a continuous map**
from a separable space, for example a ucp lift `S → B` of `θ : S → Q^ω`. -/
theorem exists_separable_purelyLarge_range {P : StarSubalgebra ℂ B → Prop}
    (hP : IsSeparablyInheritable P) (W : PurelyLargeWitnessData J)
    (hJR : ∀ b x : B, x ∈ J → x * b ∈ J) {S : Type*} [TopologicalSpace S] [SeparableSpace S]
    (σ : S → B) (hσ : Continuous σ) :
    ∃ D : StarSubalgebra ℂ B, Set.range σ ⊆ D ∧ IsSepClosed D ∧ P D ∧
      IsPurelyLargeExtension D (sepIdeal D J) := by
  obtain ⟨c, hc, hdense⟩ := exists_countable_dense S
  obtain ⟨D, hcD, hD, hPD, hPL⟩ := exists_separable_purelyLarge hP W hJR (hc.image σ)
  refine ⟨D, ?_, hD, hPD, hPL⟩
  rintro _ ⟨x, rfl⟩
  have hx : σ x ∈ closure (σ '' c) :=
    map_mem_closure hσ (hdense x) (Set.mapsTo_image σ c)
  exact closure_minimal hcD hD.1 hx

/-- The trivial property is separably inheritable. -/
theorem isSeparablyInheritable_true :
    IsSeparablyInheritable (fun _ : StarSubalgebra ℂ B => True) :=
  ⟨fun D₀ h₀ => ⟨D₀, le_rfl, h₀, trivial⟩, fun _ _ _ _ => trivial⟩

end

end GroupApproximation.Full.TWWSchafhauser
