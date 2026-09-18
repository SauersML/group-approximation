import GroupApproximation.Analysis.CStarCountableAdjoinSeparable

/-!
# Separable reduction of the obstruction extension

Lane TWWSchafhauser-3d2, work order WO-TWWSchafhauser-3d-2 (b).

Schafhauser's argument (C. Schafhauser, *A new proof of the Tikuisis--White--Winter
theorem*, J. reine angew. Math. 759 (2020), §4) works with a non-separable ambient
algebra `B` (the norm ultrapower `Q_ω` of the universal UHF algebra) and a closed
ideal `J ⊆ B` (the trace-kernel ideal).  The Ext/UCT machinery needs separable
coefficients, so one passes to a separable closed `*`-subalgebra `D ⊆ B` that contains
a countable set of data (for example the image of a lift) and to the ideal
`J_D := D ∩ J` of `D`.  The properties to be kept ("`K₁(J_D) = 0`", "`K₀(J_D)` is
torsion free and divisible", "the pulled-back extension is purely large") are all
*separably inheritable*, in the Löwenheim--Skolem sense of Blackadar, *Operator
Algebras* (2006), II.8.5:

* (step) every separable closed `D₀` sits inside a separable closed `D` with the
  property, and
* (chain) the property passes to the closure of an increasing sequence of separable
  closed subalgebras that have it.

This file proves the abstract principle:

* `isSepClosed_adjoinClosure`: a countable set generates a separable closed
  `*`-subalgebra.
* `isSepClosed_chainClosure`: the closure of an increasing sequence of separable closed
  subalgebras is separable and closed.
* `IsSeparablyInheritable.and`: two inheritable properties hold simultaneously, via an
  interleaved chain.
* `isSeparablyInheritable_of_step`: the countable-witness form of the step clause.
* `exists_separable_reduction`, `exists_separable_reduction_range`: the separable
  reduction itself.
* `sepIdeal D J := D ∩ J`, which is closed when `D` and `J` are, and is an ideal of `D`
  when `J` is an ideal of `B`.

The `K`-theoretic instances (`K₁ = 0`, `K₀` torsion free divisible) are proved against
`KOneN` / `KZeroN` in the work order WO-TWWSch-3d2-S.  The file
`ObstructionSeparableCounter.lean` shows why the ambient algebra must be built over `Q`
rather than over `∏_ω M_k`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

noncomputable section

open TopologicalSpace

variable {B : Type} [CStarAlgebra B]

/-- A `*`-subalgebra that is closed and separable. -/
def IsSepClosed (D : StarSubalgebra ℂ B) : Prop :=
  IsClosed (D : Set B) ∧ IsSeparable (D : Set B)

/-- The closure of the union of a sequence of `*`-subalgebras. -/
def chainClosure (D : ℕ → StarSubalgebra ℂ B) : StarSubalgebra ℂ B :=
  (⨆ n, D n).topologicalClosure

/-- **Separable inheritability** (Blackadar, Operator Algebras II.8.5).  A property of
`*`-subalgebras is separably inheritable if every separable closed subalgebra is
contained in a separable closed one with the property, and the property passes to
closures of increasing sequences of separable closed subalgebras with the property. -/
def IsSeparablyInheritable (P : StarSubalgebra ℂ B → Prop) : Prop :=
  (∀ D₀ : StarSubalgebra ℂ B, IsSepClosed D₀ →
      ∃ D : StarSubalgebra ℂ B, D₀ ≤ D ∧ IsSepClosed D ∧ P D) ∧
    ∀ D : ℕ → StarSubalgebra ℂ B, Monotone D → (∀ n, IsSepClosed (D n)) →
      (∀ n, P (D n)) → P (chainClosure D)

/-- A countable set generates a separable closed `*`-subalgebra. -/
theorem isSepClosed_adjoinClosure {s : Set B} (hs : s.Countable) :
    IsSepClosed (StarAlgebra.adjoin ℂ s).topologicalClosure := by
  refine ⟨StarSubalgebra.isClosed_topologicalClosure _, ?_⟩
  haveI : SeparableSpace
      (((StarAlgebra.adjoin ℂ s).topologicalClosure : StarSubalgebra ℂ B) : Set B) :=
    GroupApproximation.topologicalClosure_adjoin_separable_of_countable s hs
  exact IsSeparable.of_subtype _

/-- Every term of a sequence lies below its chain closure. -/
theorem le_chainClosure (D : ℕ → StarSubalgebra ℂ B) (n : ℕ) : D n ≤ chainClosure D :=
  (le_iSup D n).trans (StarSubalgebra.le_topologicalClosure _)

/-- The chain closure of an increasing sequence of separable closed subalgebras is
separable and closed. -/
theorem isSepClosed_chainClosure {D : ℕ → StarSubalgebra ℂ B} (hD : Monotone D)
    (hsep : ∀ n, IsSepClosed (D n)) : IsSepClosed (chainClosure D) := by
  refine ⟨StarSubalgebra.isClosed_topologicalClosure _, ?_⟩
  have h : IsSeparable (closure (⋃ n, (D n : Set B))) :=
    (IsSeparable.iUnion fun n => (hsep n).2).closure
  rw [← StarSubalgebra.coe_iSup_of_directed hD.directed_le] at h
  exact h

/-- Two interleaved sequences have the same chain closure. -/
theorem chainClosure_eq_of_interleaved {D D' : ℕ → StarSubalgebra ℂ B}
    (hDD' : ∀ n, D n ≤ D' n) (hD'D : ∀ n, D' n ≤ D (n + 1)) :
    chainClosure D = chainClosure D' := by
  have h : (⨆ n, D n) = ⨆ n, D' n :=
    le_antisymm (iSup_le fun n => (hDD' n).trans (le_iSup D' n))
      (iSup_le fun n => (hD'D n).trans (le_iSup D (n + 1)))
  exact congrArg StarSubalgebra.topologicalClosure h

/-- Enlarge a separable closed subalgebra so that it contains a countable set. -/
theorem exists_isSepClosed_le_of_countable {D₀ : StarSubalgebra ℂ B}
    (h₀ : IsSepClosed D₀) {s : Set B} (hs : s.Countable) :
    ∃ D : StarSubalgebra ℂ B, D₀ ≤ D ∧ s ⊆ D ∧ IsSepClosed D := by
  obtain ⟨c, hc, hD₀c⟩ := h₀.2
  refine ⟨(StarAlgebra.adjoin ℂ (c ∪ s)).topologicalClosure, ?_, ?_,
    isSepClosed_adjoinClosure (hc.union hs)⟩
  · intro x hx
    exact closure_mono
      (Set.Subset.trans Set.subset_union_left (StarAlgebra.subset_adjoin ℂ (c ∪ s)))
      (hD₀c hx)
  · intro x hx
    exact StarSubalgebra.le_topologicalClosure _
      (StarAlgebra.subset_adjoin ℂ (c ∪ s) (Set.mem_union_right c hx))

/-- **Inheritable properties can be combined.**  Build `a₀ ≤ b₀ ≤ a₁ ≤ b₁ ≤ ⋯` with
the first property on every `aₙ` and the second on every `bₙ`; both sequences have the
same chain closure. -/
theorem IsSeparablyInheritable.and {P P' : StarSubalgebra ℂ B → Prop}
    (hP : IsSeparablyInheritable P) (hP' : IsSeparablyInheritable P') :
    IsSeparablyInheritable fun D => P D ∧ P' D := by
  refine ⟨fun D₀ h₀ => ?_, fun D hD hsep hPD =>
    ⟨hP.2 D hD hsep fun n => (hPD n).1, hP'.2 D hD hsep fun n => (hPD n).2⟩⟩
  have hf : ∀ E : {D : StarSubalgebra ℂ B // IsSepClosed D},
      ∃ F : {D : StarSubalgebra ℂ B // IsSepClosed D}, E.1 ≤ F.1 ∧ P F.1 := by
    intro E
    obtain ⟨F, hEF, hF, hPF⟩ := hP.1 E.1 E.2
    exact ⟨⟨F, hF⟩, hEF, hPF⟩
  have hg : ∀ E : {D : StarSubalgebra ℂ B // IsSepClosed D},
      ∃ F : {D : StarSubalgebra ℂ B // IsSepClosed D}, E.1 ≤ F.1 ∧ P' F.1 := by
    intro E
    obtain ⟨F, hEF, hF, hPF⟩ := hP'.1 E.1 E.2
    exact ⟨⟨F, hF⟩, hEF, hPF⟩
  choose f hfle hfP using hf
  choose g hgle hgP using hg
  obtain ⟨a, ha0, ha⟩ : ∃ a : ℕ → {D : StarSubalgebra ℂ B // IsSepClosed D},
      a 0 = f ⟨D₀, h₀⟩ ∧ ∀ n, a (n + 1) = f (g (a n)) :=
    ⟨fun n => Nat.rec (motive := fun _ => {D : StarSubalgebra ℂ B // IsSepClosed D})
      (f ⟨D₀, h₀⟩) (fun _ E => f (g E)) n, rfl, fun _ => rfl⟩
  have hab : ∀ n, (a n).1 ≤ (g (a n)).1 := fun n => hgle (a n)
  have hba : ∀ n, (g (a n)).1 ≤ (a (n + 1)).1 := by
    intro n
    rw [ha n]
    exact hfle _
  have hmono_a : Monotone fun n => (a n).1 :=
    monotone_nat_of_le_succ fun n => (hab n).trans (hba n)
  have hmono_b : Monotone fun n => (g (a n)).1 :=
    monotone_nat_of_le_succ fun n => (hba n).trans (hab (n + 1))
  have hPa : ∀ n, P (a n).1 := by
    intro n
    cases n with
    | zero =>
      rw [ha0]
      exact hfP _
    | succ n =>
      rw [ha n]
      exact hfP _
  have heq : chainClosure (fun n => (a n).1) = chainClosure fun n => (g (a n)).1 :=
    chainClosure_eq_of_interleaved (D := fun n => (a n).1)
      (D' := fun n => (g (a n)).1) hab hba
  refine ⟨chainClosure fun n => (a n).1, ?_,
    isSepClosed_chainClosure hmono_a fun n => (a n).2, ?_, ?_⟩
  · have h0 : D₀ ≤ (a 0).1 := by
      rw [ha0]
      exact hfle ⟨D₀, h₀⟩
    exact h0.trans (le_chainClosure (fun n => (a n).1) 0)
  · exact hP.2 _ hmono_a (fun n => (a n).2) hPa
  · rw [heq]
    exact hP'.2 _ hmono_b (fun n => (g (a n)).2) fun n => hgP (a n)

/-- **The countable-witness form of the step clause.**  Suppose that for every
separable closed `D₀` there are countably many witnesses such that any larger
subalgebra containing them fixes the defects of `D₀` (the relation `step D₀ D`), and
that the property holds for the chain closure of every increasing sequence in which
each term fixes the defects of the previous one.  Then the step clause of separable
inheritability holds. -/
theorem exists_isSepClosed_of_step {P : StarSubalgebra ℂ B → Prop}
    (step : StarSubalgebra ℂ B → StarSubalgebra ℂ B → Prop)
    (hstep : ∀ D₀ : StarSubalgebra ℂ B, IsSepClosed D₀ →
      ∃ s : Set B, s.Countable ∧ ∀ D : StarSubalgebra ℂ B, D₀ ≤ D → s ⊆ D → step D₀ D)
    (hchain : ∀ D : ℕ → StarSubalgebra ℂ B, Monotone D → (∀ n, IsSepClosed (D n)) →
      (∀ n, step (D n) (D (n + 1))) → P (chainClosure D))
    (D₀ : StarSubalgebra ℂ B) (h₀ : IsSepClosed D₀) :
    ∃ D : StarSubalgebra ℂ B, D₀ ≤ D ∧ IsSepClosed D ∧ P D := by
  have hnext : ∀ E : {D : StarSubalgebra ℂ B // IsSepClosed D},
      ∃ F : {D : StarSubalgebra ℂ B // IsSepClosed D}, E.1 ≤ F.1 ∧ step E.1 F.1 := by
    intro E
    obtain ⟨s, hs, hsD⟩ := hstep E.1 E.2
    obtain ⟨F, hEF, hsF, hF⟩ := exists_isSepClosed_le_of_countable E.2 hs
    exact ⟨⟨F, hF⟩, hEF, hsD F hEF hsF⟩
  choose next hle hst using hnext
  obtain ⟨a, ha0, ha⟩ : ∃ a : ℕ → {D : StarSubalgebra ℂ B // IsSepClosed D},
      a 0 = ⟨D₀, h₀⟩ ∧ ∀ n, a (n + 1) = next (a n) :=
    ⟨fun n => Nat.rec (motive := fun _ => {D : StarSubalgebra ℂ B // IsSepClosed D})
      ⟨D₀, h₀⟩ (fun _ E => next E) n, rfl, fun _ => rfl⟩
  have hsucc : ∀ n, (a n).1 ≤ (a (n + 1)).1 := by
    intro n
    rw [ha n]
    exact hle _
  have hmono : Monotone fun n => (a n).1 := monotone_nat_of_le_succ hsucc
  have hsteps : ∀ n, step (a n).1 (a (n + 1)).1 := by
    intro n
    rw [ha n]
    exact hst _
  refine ⟨chainClosure fun n => (a n).1, ?_,
    isSepClosed_chainClosure hmono fun n => (a n).2, hchain _ hmono (fun n => (a n).2) hsteps⟩
  have h0 : D₀ ≤ (a 0).1 := (congrArg Subtype.val ha0).symm.le
  exact h0.trans (le_chainClosure (fun n => (a n).1) 0)

/-- Separable inheritability from countable witnesses and continuity along chains. -/
theorem isSeparablyInheritable_of_step {P : StarSubalgebra ℂ B → Prop}
    (step : StarSubalgebra ℂ B → StarSubalgebra ℂ B → Prop)
    (hstep : ∀ D₀ : StarSubalgebra ℂ B, IsSepClosed D₀ →
      ∃ s : Set B, s.Countable ∧ ∀ D : StarSubalgebra ℂ B, D₀ ≤ D → s ⊆ D → step D₀ D)
    (hchain : ∀ D : ℕ → StarSubalgebra ℂ B, Monotone D → (∀ n, IsSepClosed (D n)) →
      (∀ n, step (D n) (D (n + 1))) → P (chainClosure D))
    (hcont : ∀ D : ℕ → StarSubalgebra ℂ B, Monotone D → (∀ n, IsSepClosed (D n)) →
      (∀ n, P (D n)) → P (chainClosure D)) :
    IsSeparablyInheritable P :=
  ⟨exists_isSepClosed_of_step step hstep hchain, hcont⟩

/-- **Separable reduction.**  For a separably inheritable property and a countable set
`s ⊆ B`, there is a separable closed `*`-subalgebra `D ⊇ s` with the property. -/
theorem exists_separable_reduction {P : StarSubalgebra ℂ B → Prop}
    (hP : IsSeparablyInheritable P) {s : Set B} (hs : s.Countable) :
    ∃ D : StarSubalgebra ℂ B, s ⊆ D ∧ IsSepClosed D ∧ P D := by
  obtain ⟨D, hD₀, hD, hPD⟩ := hP.1 _ (isSepClosed_adjoinClosure hs)
  refine ⟨D, fun x hx => hD₀ ?_, hD, hPD⟩
  exact StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ s hx)

/-- **Separable reduction containing the range of a continuous map** from a separable
space, for example a ucp lift `S → B` of a separable `S`. -/
theorem exists_separable_reduction_range {P : StarSubalgebra ℂ B → Prop}
    (hP : IsSeparablyInheritable P) {S : Type*} [TopologicalSpace S] [SeparableSpace S]
    (σ : S → B) (hσ : Continuous σ) :
    ∃ D : StarSubalgebra ℂ B, Set.range σ ⊆ D ∧ IsSepClosed D ∧ P D := by
  obtain ⟨c, hc, hdense⟩ := exists_countable_dense S
  obtain ⟨D, hcD, hD, hPD⟩ := exists_separable_reduction hP (hc.image σ)
  refine ⟨D, ?_, hD, hPD⟩
  rintro _ ⟨x, rfl⟩
  have hx : σ x ∈ closure (σ '' c) :=
    map_mem_closure hσ (hdense x) fun y hy => Set.mem_image_of_mem σ hy
  exact closure_minimal hcD hD.1 hx

/-- The ideal `J_D := D ∩ J` cut out of `J` by a subalgebra `D`. -/
def sepIdeal (D : StarSubalgebra ℂ B) (J : NonUnitalStarSubalgebra ℂ B) :
    NonUnitalStarSubalgebra ℂ B :=
  D.toNonUnitalStarSubalgebra ⊓ J

theorem mem_sepIdeal {D : StarSubalgebra ℂ B} {J : NonUnitalStarSubalgebra ℂ B} {x : B} :
    x ∈ sepIdeal D J ↔ x ∈ D ∧ x ∈ J :=
  NonUnitalStarSubalgebra.mem_inf

theorem isClosed_sepIdeal {D : StarSubalgebra ℂ B} {J : NonUnitalStarSubalgebra ℂ B}
    (hD : IsClosed (D : Set B)) (hJ : IsClosed (J : Set B)) :
    IsClosed (sepIdeal D J : Set B) := by
  rw [sepIdeal, NonUnitalStarSubalgebra.coe_inf]
  exact hD.inter hJ

/-- `J_D` is a left ideal of `D` when `J` is a left ideal of `B`. -/
theorem mul_mem_sepIdeal_left {D : StarSubalgebra ℂ B} {J : NonUnitalStarSubalgebra ℂ B}
    (hJ : ∀ b x : B, x ∈ J → b * x ∈ J) {d x : B} (hd : d ∈ D) (hx : x ∈ sepIdeal D J) :
    d * x ∈ sepIdeal D J :=
  mem_sepIdeal.mpr ⟨mul_mem hd (mem_sepIdeal.mp hx).1, hJ d x (mem_sepIdeal.mp hx).2⟩

/-- `J_D` is a right ideal of `D` when `J` is a right ideal of `B`. -/
theorem mul_mem_sepIdeal_right {D : StarSubalgebra ℂ B} {J : NonUnitalStarSubalgebra ℂ B}
    (hJ : ∀ b x : B, x ∈ J → x * b ∈ J) {d x : B} (hd : d ∈ D) (hx : x ∈ sepIdeal D J) :
    x * d ∈ sepIdeal D J :=
  mem_sepIdeal.mpr ⟨mul_mem (mem_sepIdeal.mp hx).1 hd, hJ d x (mem_sepIdeal.mp hx).2⟩

/-- `J_D` is separable when `D` is. -/
theorem isSeparable_sepIdeal {D : StarSubalgebra ℂ B} {J : NonUnitalStarSubalgebra ℂ B}
    (hD : IsSepClosed D) : IsSeparable (sepIdeal D J : Set B) :=
  hD.2.mono fun _ hx => (mem_sepIdeal.mp hx).1

end

end GroupApproximation.Full.TWWSchafhauser
