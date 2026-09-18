import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.HKTAlgebraDef

/-!
# Ideals of the HKT algebra supported on a subset

Lane TWWUCT-E (WO-TWWUCT-E), manuscript label `thm:fixed-radical-membership` (UCT input,
`non_mf_group_notes.tex` L1370--1378).  Higson--Kasparov (Invent. Math. 144 (2001), §9) and
Tu (K-Theory 17 (1999), Prop. 10.7) prove that the proper crossed product `A(H) ⋊_r G` lies in the
bootstrap class.  They exhaust the proper `G`-space `ℝ × H` by `G`-invariant open sets `W` and use
the ideals `I_W ⊆ A(H)` of functions vanishing off `W`.  This file defines these ideals.

* `VanishesOff W f`: the element `f` of `A(H)` vanishes on the complement of `W`.
* `hktIdeal C W`: the closed two-sided ⋆-ideal of such elements.
* `HKTIdealOf C W`: its carrier, a `NonUnitalCStarAlgebra`.
-/

namespace GroupApproximation.Full.TWWUCT

noncomputable section

universe v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {C : Type w} [CStarAlgebra C] [CliffordSystem H C]

/-- The element `f ∈ A(H)` vanishes off `W ⊆ ℝ × H`.  This is the support condition that defines
the ideals `I_W` in the exhaustion argument for `thm:fixed-radical-membership` (UCT input). -/
def VanishesOff (W : Set (ℝ × H)) (f : HKTAlgebraOf H C) : Prop :=
  ∀ x : ℝ × H, x ∉ W → (f : ℝ × H →ᵇ C) x = 0

variable (C) in
/-- The ideal `I_W ⊆ A(H)` of elements vanishing off `W`, as a ⋆-subalgebra
(Higson--Kasparov 2001, §9; used for `thm:fixed-radical-membership`, UCT input). -/
def hktIdeal (W : Set (ℝ × H)) : NonUnitalStarSubalgebra ℂ (HKTAlgebraOf H C) where
  carrier := {f | VanishesOff W f}
  add_mem' := by
    intro f g hf hg
    have hf' : VanishesOff W f := hf
    have hg' : VanishesOff W g := hg
    show VanishesOff W (f + g)
    intro x hx
    calc ((f + g : HKTAlgebraOf H C) : ℝ × H →ᵇ C) x
        = (f : ℝ × H →ᵇ C) x + (g : ℝ × H →ᵇ C) x := rfl
      _ = 0 := by rw [hf' x hx, hg' x hx, add_zero]
  zero_mem' := by
    show VanishesOff W (0 : HKTAlgebraOf H C)
    intro x _
    rfl
  mul_mem' := by
    intro f g hf _
    have hf' : VanishesOff W f := hf
    show VanishesOff W (f * g)
    intro x hx
    calc ((f * g : HKTAlgebraOf H C) : ℝ × H →ᵇ C) x
        = (f : ℝ × H →ᵇ C) x * (g : ℝ × H →ᵇ C) x := rfl
      _ = 0 := by rw [hf' x hx, zero_mul]
  smul_mem' := by
    intro c f hf
    have hf' : VanishesOff W f := hf
    show VanishesOff W (c • f)
    intro x hx
    calc ((c • f : HKTAlgebraOf H C) : ℝ × H →ᵇ C) x
        = c • (f : ℝ × H →ᵇ C) x := rfl
      _ = 0 := by rw [hf' x hx, smul_zero]
  star_mem' := by
    intro f hf
    have hf' : VanishesOff W f := hf
    show VanishesOff W (star f)
    intro x hx
    calc ((star f : HKTAlgebraOf H C) : ℝ × H →ᵇ C) x
        = star ((f : ℝ × H →ᵇ C) x) := rfl
      _ = 0 := by rw [hf' x hx, star_zero]

/-- Membership in `I_W` (`thm:fixed-radical-membership`, UCT input). -/
theorem mem_hktIdeal {W : Set (ℝ × H)} {f : HKTAlgebraOf H C} :
    f ∈ hktIdeal C W ↔ VanishesOff W f :=
  Iff.rfl

/-- `I_W` is a left ideal of `A(H)` (`thm:fixed-radical-membership`, UCT input). -/
theorem mul_mem_hktIdeal_left {W : Set (ℝ × H)} (a : HKTAlgebraOf H C)
    {f : HKTAlgebraOf H C} (hf : f ∈ hktIdeal C W) : a * f ∈ hktIdeal C W := by
  have hf' : VanishesOff W f := hf
  show VanishesOff W (a * f)
  intro x hx
  calc ((a * f : HKTAlgebraOf H C) : ℝ × H →ᵇ C) x
      = (a : ℝ × H →ᵇ C) x * (f : ℝ × H →ᵇ C) x := rfl
    _ = 0 := by rw [hf' x hx, mul_zero]

/-- `I_W` is a right ideal of `A(H)` (`thm:fixed-radical-membership`, UCT input). -/
theorem mul_mem_hktIdeal_right {W : Set (ℝ × H)} {f : HKTAlgebraOf H C}
    (hf : f ∈ hktIdeal C W) (a : HKTAlgebraOf H C) : f * a ∈ hktIdeal C W := by
  have hf' : VanishesOff W f := hf
  show VanishesOff W (f * a)
  intro x hx
  calc ((f * a : HKTAlgebraOf H C) : ℝ × H →ᵇ C) x
      = (f : ℝ × H →ᵇ C) x * (a : ℝ × H →ᵇ C) x := rfl
    _ = 0 := by rw [hf' x hx, zero_mul]

/-- `I_W ⊆ I_{W'}` for `W ⊆ W'`: the exhaustion `I_{W_n} ⊆ I_{W_{n+1}}`
(`thm:fixed-radical-membership`, UCT input). -/
theorem hktIdeal_mono {W W' : Set (ℝ × H)} (hW : W ⊆ W') : hktIdeal C W ≤ hktIdeal C W' := by
  intro f hf
  have hf' : VanishesOff W f := hf
  show VanishesOff W' f
  intro x hx
  exact hf' x (fun hxW => hx (hW hxW))

/-- `I_{ℝ × H} = A(H)` (`thm:fixed-radical-membership`, UCT input). -/
theorem hktIdeal_univ : hktIdeal C (Set.univ : Set (ℝ × H)) = ⊤ := by
  refine eq_top_iff.2 fun f _ => ?_
  show VanishesOff Set.univ f
  intro x hx
  exact absurd (Set.mem_univ x) hx

/-- `I_{W ∩ W'} = I_W ⊓ I_{W'}` (`thm:fixed-radical-membership`, UCT input). -/
theorem hktIdeal_inter (W W' : Set (ℝ × H)) :
    hktIdeal C (W ∩ W') = hktIdeal C W ⊓ hktIdeal C W' := by
  refine le_antisymm (le_inf (hktIdeal_mono Set.inter_subset_left)
    (hktIdeal_mono Set.inter_subset_right)) ?_
  intro f hf
  have h1 : VanishesOff W f := (NonUnitalStarSubalgebra.mem_inf.1 hf).1
  have h2 : VanishesOff W' f := (NonUnitalStarSubalgebra.mem_inf.1 hf).2
  show VanishesOff (W ∩ W') f
  intro x hx
  by_cases hxW : x ∈ W
  · exact h2 x (fun hxW' => hx ⟨hxW, hxW'⟩)
  · exact h1 x hxW

/-- The set of elements of `A(H)` vanishing off `W` is an intersection of zero sets of point
evaluations (`thm:fixed-radical-membership`, UCT input). -/
theorem coe_hktIdeal_eq_iInter (W : Set (ℝ × H)) :
    (hktIdeal C W : Set (HKTAlgebraOf H C)) =
      ⋂ x ∈ Wᶜ, {f : HKTAlgebraOf H C | (f : ℝ × H →ᵇ C) x = 0} := by
  ext f
  rw [Set.mem_iInter₂]
  constructor
  · intro hf x hx
    have hf' : VanishesOff W f := hf
    exact hf' x hx
  · intro hf
    show VanishesOff W f
    intro x hx
    exact hf x hx

/-- `I_W` is closed in `A(H)` (`thm:fixed-radical-membership`, UCT input). -/
instance isClosed_hktIdeal (W : Set (ℝ × H)) :
    IsClosed (hktIdeal C W : Set (HKTAlgebraOf H C)) := by
  rw [coe_hktIdeal_eq_iInter]
  refine isClosed_biInter fun x _ => ?_
  have hev : Continuous fun f : HKTAlgebraOf H C => (f : ℝ × H →ᵇ C) x :=
    Continuous.eval_const (f := fun f : HKTAlgebraOf H C => (f : ℝ × H →ᵇ C))
      continuous_subtype_val x
  exact isClosed_eq hev continuous_const

variable (C) in
/-- The carrier of the ideal `I_W` (`thm:fixed-radical-membership`, UCT input). -/
abbrev HKTIdealOf (W : Set (ℝ × H)) :=
  ↥(hktIdeal C W)

/-- `I_W` is a non-unital C⋆-algebra (`thm:fixed-radical-membership`, UCT input). -/
noncomputable instance instNonUnitalCStarAlgebraHKTIdealOf (W : Set (ℝ × H)) :
    NonUnitalCStarAlgebra (HKTIdealOf C W) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (hktIdeal C W)

end

end GroupApproximation.Full.TWWUCT
