import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Common zeros of sections of the tautological bundle over `ℂPᴺ`

The counterexample to Problem XXII of Schafhauser--Tikuisis--White needs one
purely topological input, recorded in Section 2 of
`research/artifacts/stw22-trace-problem-counterexample-audit-2026-08-31.md`:

> if `s * ℓ ≤ s²` then any `ℓ` continuous sections of `L^{⊕s}` over `ℂP^(s²)`
> have a common zero, where `L` is the tautological line bundle.

Mathlib has no vector bundles and no characteristic classes, so this file
carries the statement in *homogeneous coordinates*, where no bundle language is
needed at all.

## The dictionary

A continuous section `σ` of `L` over `ℂPᴺ` assigns to each line `[z]` a vector
`σ [z] ∈ ℂz`, so it is exactly a continuous `g : ℂ^{N+1} ∖ {0} → ℂ` with
`σ [z] = g z • z`; well-definedness of `σ` on the line through `z` forces
`g (c • z) * c = g z`, i.e. homogeneity of degree `-1`.  A section of the
`κ`-fold sum `L^{⊕κ}` is the same thing with values in `κ → ℂ`, and the section
vanishes at `[z]` exactly when the corresponding vector `g z` vanishes.  This is
the content of `TautSection` below; nothing in the file depends on the reader
accepting the dictionary, because every later statement is phrased in the
homogeneous-coordinate language.

## Model tests

`TautSection` is inhabited by the zero section (`TautSection.zero`), so no
statement here is vacuous.  The two boundary cases were checked before the
statements were fixed:

* `κ` empty: every section is the zero section and the conclusion is trivially
  true, matching `Nat.card κ = 0 ≤ N`.
* `N = 0`, `κ = Unit`: `ℂP⁰` is a point, `L` is trivial there and
  `z ↦ (z 0)⁻¹` is a *nowhere-vanishing* section.  This is `unitSection` below,
  and `not_forall_exists_zero` turns it into a refutation of the statement one
  gets by relaxing the rank bound by one.  So the hypothesis `Nat.card κ ≤ N`
  in `CommonZeroProperty` is sharp, not decorative.
* `κ` infinite: `Nat.card κ = 0`, so a `Nat.card`-only hypothesis would claim a
  common zero for infinite-rank sums; but padding a nowhere-zero section of
  `L^{⊕(N+1)}` with zeros gives a nowhere-zero section of `L^{⊕ℕ}`.  This is
  why `CommonZeroProperty` carries `Finite κ` as a separate hypothesis rather
  than reading finiteness off the cardinality bound.

## Main declarations

* `TautSection N κ` -- a continuous section of `L^{⊕κ}` over `ℂPᴺ`.
* `join` -- a family of `ι` sections of `L^{⊕κ}` is one section of
  `L^{⊕(ι × κ)}`; `hasCommonZero_iff_join` says a common zero of the family is
  a zero of the join.  This is the step "`c = (c₁,…,c_ℓ)` is a section of
  `L^{⊕(sℓ)}`" of the audit, and it is proved here.
* `CommonZeroProperty` -- the topological input itself, as a named `Prop`.
* `hasCommonZero_of_le` -- the exact instance the audit consumes.

The rank-one case of `CommonZeroProperty` is *proved* in
`GroupApproximation.Topology.TautologicalLineWinding`.  The general case is the
Chern-class statement and is not available from Mathlib; it is deliberately
left as a hypothesis rather than an axiom, so every consumer carries it
visibly.
-/

namespace GroupApproximation
namespace TautologicalCommonZero

/-- Homogeneous coordinates for `ℂPᴺ`: the punctured space `ℂ^{N+1} ∖ {0}`. -/
def punctured (N : ℕ) : Set (Fin (N + 1) → ℂ) := {z | z ≠ 0}

@[simp]
theorem mem_punctured {N : ℕ} {z : Fin (N + 1) → ℂ} :
    z ∈ punctured N ↔ z ≠ 0 := Iff.rfl

/-- A continuous section of the `κ`-fold direct sum `L^{⊕κ}` of the tautological
line bundle over `ℂPᴺ`, written in homogeneous coordinates: a continuous map on
`ℂ^{N+1} ∖ {0}` which is homogeneous of degree `-1`. -/
structure TautSection (N : ℕ) (κ : Type*) where
  /-- The section read in homogeneous coordinates. -/
  toFun : (Fin (N + 1) → ℂ) → κ → ℂ
  /-- Sections are continuous away from the origin of the homogeneous
  coordinates. -/
  continuousOn_toFun : ContinuousOn toFun (punctured N)
  /-- Degree `-1` homogeneity: this is exactly well-definedness of
  `[z] ↦ toFun z • z` on projective space. -/
  homogeneous : ∀ (c : ℂ) (z : Fin (N + 1) → ℂ), c ≠ 0 → z ≠ 0 →
      toFun (c • z) = c⁻¹ • toFun z

namespace TautSection

/-- The zero section.  Its presence shows that no statement about
`TautSection` is vacuous. -/
def zero (N : ℕ) (κ : Type*) : TautSection N κ where
  toFun := fun _ => 0
  continuousOn_toFun := continuousOn_const
  homogeneous := fun _ _ _ _ => by simp

instance (N : ℕ) (κ : Type*) : Inhabited (TautSection N κ) := ⟨zero N κ⟩

/-- One scalar component of a section. -/
def component {N : ℕ} {κ : Type*} (f : TautSection N κ) (k : κ) :
    (Fin (N + 1) → ℂ) → ℂ := fun z => f.toFun z k

theorem continuousOn_component {N : ℕ} {κ : Type*} (f : TautSection N κ) (k : κ) :
    ContinuousOn (f.component k) (punctured N) :=
  (continuous_apply k).comp_continuousOn' f.continuousOn_toFun

theorem component_smul {N : ℕ} {κ : Type*} (f : TautSection N κ) (k : κ)
    (c : ℂ) (z : Fin (N + 1) → ℂ) (hc : c ≠ 0) (hz : z ≠ 0) :
    f.component k (c • z) = c⁻¹ * f.component k z := by
  have h := congrFun (f.homogeneous c z hc hz) k
  simpa [component] using h

end TautSection

/-- A family of sections has a common zero away from the origin of the
homogeneous coordinates. -/
def HasCommonZero {N : ℕ} {ι κ : Type*} (F : ι → TautSection N κ) : Prop :=
  ∃ z : Fin (N + 1) → ℂ, z ≠ 0 ∧ ∀ j, (F j).toFun z = 0

/-- The direct sum of a family of sections: `ι` sections of `L^{⊕κ}` assemble
into one section of `L^{⊕(ι × κ)}`.  This is the audit's step
"`c = (c₁,…,c_ℓ)` is a section of `L^{⊕(sℓ)}`". -/
def join {N : ℕ} {ι κ : Type*} (F : ι → TautSection N κ) : TautSection N (ι × κ) where
  toFun := fun z p => (F p.1).toFun z p.2
  continuousOn_toFun := by
    refine continuousOn_pi' fun p => ?_
    exact (F p.1).continuousOn_component p.2
  homogeneous := fun c z hc hz => by
    funext p
    have h := (F p.1).component_smul p.2 c z hc hz
    simpa [TautSection.component] using h

@[simp]
theorem join_toFun {N : ℕ} {ι κ : Type*} (F : ι → TautSection N κ)
    (z : Fin (N + 1) → ℂ) (p : ι × κ) :
    (join F).toFun z p = (F p.1).toFun z p.2 := rfl

/-- A common zero of a family is exactly a zero of its direct sum. -/
theorem hasCommonZero_iff_join {N : ℕ} {ι κ : Type*} (F : ι → TautSection N κ) :
    HasCommonZero F ↔ ∃ z : Fin (N + 1) → ℂ, z ≠ 0 ∧ (join F).toFun z = 0 := by
  constructor
  · rintro ⟨z, hz, h⟩
    exact ⟨z, hz, funext fun p => by simp [h p.1]⟩
  · rintro ⟨z, hz, h⟩
    refine ⟨z, hz, fun j => funext fun k => ?_⟩
    have hjk := congrFun h (j, k)
    simpa using hjk

/-- **The common-zero property.**  Over `ℂPᴺ`, a section of a direct sum of at
most `N` copies of the tautological line bundle has a zero.

This is the Chern-class input of Section 2 of the STW Problem XXII audit: the
top Chern class of `L^{⊕k}` is `(±u)^k`, which is nonzero in
`H^{2k}(ℂPᴺ; ℤ)` exactly when `k ≤ N`, and a nowhere-zero section would split
off a trivial line and kill it.

Both hypotheses are load-bearing; see the module docstring for the two
refuting instances. -/
def CommonZeroProperty : Prop :=
  ∀ (N : ℕ) (κ : Type) (_ : Finite κ), Nat.card κ ≤ N →
    ∀ f : TautSection N κ, ∃ z : Fin (N + 1) → ℂ, z ≠ 0 ∧ f.toFun z = 0

/-- The family form: `ℓ` sections of `L^{⊕s}` over `ℂPᴺ` have a common zero as
soon as `ℓ * s ≤ N`. -/
theorem hasCommonZero_of_property (h : CommonZeroProperty) {N ℓ s : ℕ}
    (hle : ℓ * s ≤ N) (F : Fin ℓ → TautSection N (Fin s)) :
    HasCommonZero F := by
  rw [hasCommonZero_iff_join]
  refine h N (Fin ℓ × Fin s) inferInstance ?_ (join F)
  rw [Nat.card_prod, Nat.card_fin, Nat.card_fin]
  exact hle

/-- **The instance consumed by the STW Problem XXII counterexample.**  Over
`ℂP^(s²)`, any `ℓ ≤ s` continuous sections of `L^{⊕s}` have a common zero. -/
theorem hasCommonZero_of_le (h : CommonZeroProperty) {s ℓ : ℕ} (hls : ℓ ≤ s)
    (F : Fin ℓ → TautSection (s * s) (Fin s)) :
    HasCommonZero F :=
  hasCommonZero_of_property h (Nat.mul_le_mul hls (le_refl s)) F

/-! ### Sharpness of the rank bound

Over `ℂP⁰` the tautological bundle is trivial and has a nowhere-vanishing
section, so `CommonZeroProperty` fails the moment the rank bound is relaxed. -/

theorem apply_ne_zero_of_ne_zero {z : Fin (0 + 1) → ℂ} (hz : z ≠ 0) : z 0 ≠ 0 := by
  haveI : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
  intro h
  apply hz
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  rw [hi]
  simpa using h

/-- The nowhere-vanishing section of the (trivial) tautological line bundle
over `ℂP⁰`. -/
noncomputable def unitSection : TautSection 0 (Fin 1) where
  toFun := fun z _ => (z 0)⁻¹
  continuousOn_toFun := by
    refine continuousOn_pi' fun _ => ?_
    exact ContinuousOn.inv₀ (continuous_apply (0 : Fin (0 + 1))).continuousOn
      fun _ hz => apply_ne_zero_of_ne_zero hz
  homogeneous := fun _ _ _ _ => by
    funext _
    simp [mul_inv]

theorem unitSection_ne_zero {z : Fin (0 + 1) → ℂ} (hz : z ≠ 0) :
    unitSection.toFun z ≠ 0 := by
  intro h
  have h0 : ((z 0)⁻¹ : ℂ) = 0 := congrFun h 0
  exact inv_ne_zero (apply_ne_zero_of_ne_zero hz) h0

/-- The rank bound in `CommonZeroProperty` cannot be relaxed by even one: the
statement with `Nat.card κ ≤ N + 1` in place of `Nat.card κ ≤ N` is false. -/
theorem not_forall_exists_zero :
    ¬ ∀ (N : ℕ) (κ : Type) (_ : Finite κ), Nat.card κ ≤ N + 1 →
        ∀ f : TautSection N κ, ∃ z : Fin (N + 1) → ℂ, z ≠ 0 ∧ f.toFun z = 0 := by
  intro h
  obtain ⟨z, hz, hzero⟩ :=
    h 0 (Fin 1) inferInstance (Nat.card_fin 1).le unitSection
  exact unitSection_ne_zero hz hzero

end TautologicalCommonZero
end GroupApproximation
