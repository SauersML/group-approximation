import GroupApproximation.GGT.DGOWindmillDef

/-!
# The windmills exhaust the rotation closure

The second of the two obligations `GGT/DGOWindmillTheorem53.lean` reduces DGO's
Theorem 5.3(b) to.  Given the growth step -- every windmill sits inside a larger
one, with a fixed gain of `10δ` -- every element of the subgroup the rotations
generate already lies in the group of *some* windmill.

## Why this is not immediate

The obvious route fails: "`g` is a product of finitely many rotations, so take a
windmill containing their apices" needs the windmills containing two given apices
to be **comparable**, and two windmills produced independently need not be.  So
the proof does not quantify over windmills at all; it builds one increasing
chain, by iterating the growth step from the ball of radius `100δ` about a fixed
apex, and shows every apex enters the chain.  Directedness is then `max`.

Two smaller obstacles, both settled here.

* **The chain has to carry its own proofs.** `growChain` lands in the subtype
  `{W // IsWindmill …}` rather than in `Set X`: a recursion whose step needs the
  previous term to be a windmill cannot be defined separately from the induction
  proving it is one.  `Exists.choose` supplies the successor and
  `Exists.choose_spec` its two clauses.
* **The rotation closure is a `normalClosure`, and closure induction wants a
  plain `closure`.**  They coincide here: `normalClosure s` is by definition
  `closure (conjugatesOfSet s)`, and the rotation generating set is closed under
  conjugation, because `rot_equivariant` and the `G`-invariance of the apex set
  give `a · Rot(c) · a⁻¹ = Rot (a • c)`.  So `conjugatesOfSet` is the identity on
  it and the two closures agree.  `rotationNormalClosure_eq_closure` records
  this; it is the only place the equivariance clause of `IsRotatingFamily` is
  used in this file.

## The statement is `WindmillExhaustion` unfolded

`GGT/DGOWindmillTheorem53.lean` is being edited by another session as this is
written, so this module imports only `GGT/DGOWindmillDef.lean` and states the
growth hypothesis and the exhaustion conclusion in unfolded form.  Both are
definitionally the named `Prop`s, so the bridge is the identity: once the two
files meet, `windmillExhaustion_of_growth` discharges `WindmillExhaustion` with
no adapter.
-/

namespace GroupApproximation
namespace DGOWindmill

open GroupApproximation.HullGeometry
open GroupApproximation.HullSC

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-! ## The rotation closure is an ordinary closure -/

/-- **The rotation generating set is closed under conjugation.**  A conjugate of
a rotation about `c` is a rotation about the conjugated apex, and the apex set is
`G`-invariant. -/
theorem conj_mem_rotationGenerators {C : Set X} {Rot : X → Subgroup G}
    (hfam : IsRotatingFamily G X C Rot) (a : G) {g : G}
    (hg : g ∈ {h : G | ∃ c ∈ C, h ∈ Rot c}) :
    a * g * a⁻¹ ∈ {h : G | ∃ c ∈ C, h ∈ Rot c} := by
  obtain ⟨c, hc, hgc⟩ := hg
  refine ⟨a • c, hfam.apex_smul a hc, ?_⟩
  rw [hfam.rot_equivariant a hc (a * g * a⁻¹)]
  have hsimp : a⁻¹ * (a * g * a⁻¹) * a = g := by group
  rw [hsimp]
  exact hgc

/-- **The subgroup the rotations generate is an ordinary closure.**

`Subgroup.normalClosure s` is `Subgroup.closure (conjugatesOfSet s)`, and the
rotation generating set absorbs its own conjugates, so the two closures agree.
This is what lets `Subgroup.closure_induction` be used on the rotation closure
below. -/
theorem rotationNormalClosure_eq_closure {C : Set X} {Rot : X → Subgroup G}
    (hfam : IsRotatingFamily G X C Rot) :
    rotationNormalClosure C Rot =
      Subgroup.closure {h : G | ∃ c ∈ C, h ∈ Rot c} := by
  have hconj : Group.conjugatesOfSet {h : G | ∃ c ∈ C, h ∈ Rot c}
      = {h : G | ∃ c ∈ C, h ∈ Rot c} := by
    refine Set.Subset.antisymm ?_ Group.subset_conjugatesOfSet
    intro x hx
    obtain ⟨a, ha, hconjax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨u, hu⟩ := isConj_iff.mp hconjax
    rw [← hu]
    exact conj_mem_rotationGenerators hfam u ha
  show Subgroup.closure (Group.conjugatesOfSet {h : G | ∃ c ∈ C, h ∈ Rot c}) = _
  rw [hconj]

/-! ## The chain of windmills -/

/-- The growth step, unfolded.  Definitionally `WindmillGrowth` as
`GGT/DGOWindmillTheorem53.lean` states it; named here so this file need not
import that one while it is being edited elsewhere. -/
def GrowthStep (δ : ℝ) (C : Set X) (Rot : X → Subgroup G) : Prop :=
  ∀ W : Set X, IsWindmill G X δ C Rot W →
    ∃ W' : Set X, IsWindmill G X δ C Rot W' ∧ thicken W (10 * δ) ⊆ W'

/-- **The increasing chain of windmills**, obtained by iterating the growth step.

It lands in the subtype rather than in `Set X` because the recursion's step needs
the previous term's windmill proof; carrying the proof alongside the set is what
makes the definition non-mutual. -/
noncomputable def growChain {δ : ℝ} {C : Set X} {Rot : X → Subgroup G}
    (hgrow : GrowthStep δ C Rot) {W₀ : Set X}
    (hW₀ : IsWindmill G X δ C Rot W₀) :
    ℕ → {W : Set X // IsWindmill G X δ C Rot W}
  | 0 => ⟨W₀, hW₀⟩
  | n + 1 =>
      ⟨(hgrow (growChain hgrow hW₀ n).1 (growChain hgrow hW₀ n).2).choose,
        (hgrow (growChain hgrow hW₀ n).1 (growChain hgrow hW₀ n).2).choose_spec.1⟩

variable {δ : ℝ} {C : Set X} {Rot : X → Subgroup G}

/-- Each step of the chain contains the `10δ`-thickening of its predecessor. -/
theorem thicken_growChain_subset (hgrow : GrowthStep δ C Rot) {W₀ : Set X}
    (hW₀ : IsWindmill G X δ C Rot W₀) (n : ℕ) :
    thicken (growChain hgrow hW₀ n).1 (10 * δ) ⊆ (growChain hgrow hW₀ (n + 1)).1 :=
  (hgrow (growChain hgrow hW₀ n).1 (growChain hgrow hW₀ n).2).choose_spec.2

/-- The chain is increasing, one step at a time. -/
theorem growChain_subset_succ (hδ : 0 < δ) (hgrow : GrowthStep δ C Rot) {W₀ : Set X}
    (hW₀ : IsWindmill G X δ C Rot W₀) (n : ℕ) :
    (growChain hgrow hW₀ n).1 ⊆ (growChain hgrow hW₀ (n + 1)).1 :=
  fun _ hx => thicken_growChain_subset hgrow hW₀ n (subset_thicken (by linarith) hx)

/-- The chain is increasing. -/
theorem growChain_mono (hδ : 0 < δ) (hgrow : GrowthStep δ C Rot) {W₀ : Set X}
    (hW₀ : IsWindmill G X δ C Rot W₀) {n m : ℕ} (hnm : n ≤ m) :
    (growChain hgrow hW₀ n).1 ⊆ (growChain hgrow hW₀ m).1 := by
  induction m with
  | zero =>
      have hn0 : n = 0 := Nat.le_zero.mp hnm
      subst hn0
      exact fun _ hx => hx
  | succ k ih =>
      rcases Nat.lt_or_ge n (k + 1) with hlt | hge
      · exact fun x hx =>
          growChain_subset_succ hδ hgrow hW₀ k (ih (Nat.lt_succ_iff.mp hlt) hx)
      · have hnk : n = k + 1 := le_antisymm hnm hge
        subst hnk
        exact fun _ hx => hx

/-! ## The chain exhausts the space -/

/-- **The chain swallows every ball about the base apex.**  Each step gains
`10δ`, and in a geodesic space a ball thickens to a bigger ball. -/
theorem closedBall_subset_growChain (hδ : 0 < δ) (hgeo : IsGeodesicSpace X)
    (hgrow : GrowthStep δ C Rot) {W₀ : Set X}
    (hW₀ : IsWindmill G X δ C Rot W₀) {c₀ : X} (hbase : W₀ = Metric.closedBall c₀ (100 * δ)) (n : ℕ) :
    Metric.closedBall c₀ (100 * δ + 10 * δ * n) ⊆ (growChain hgrow hW₀ n).1 := by
  induction n with
  | zero =>
      intro x hx
      have hr : 100 * δ + 10 * δ * ((0 : ℕ) : ℝ) = 100 * δ := by
        push_cast
        ring
      rw [hr] at hx
      show x ∈ W₀
      rw [hbase]
      exact hx
  | succ k ih =>
      have hstep : Metric.closedBall c₀ (100 * δ + 10 * δ * ((k + 1 : ℕ) : ℝ))
          ⊆ thicken (Metric.closedBall c₀ (100 * δ + 10 * δ * (k : ℕ))) (10 * δ) := by
        have hr : 100 * δ + 10 * δ * ((k + 1 : ℕ) : ℝ)
            = (100 * δ + 10 * δ * (k : ℕ)) + 10 * δ := by
          push_cast
          ring
        rw [hr]
        refine closedBall_subset_thicken_closedBall hgeo c₀ ?_ (by linarith)
        have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        nlinarith
      refine subset_trans hstep ?_
      exact subset_trans (thicken_mono_set ih) (thicken_growChain_subset hgrow hW₀ k)

/-- **Every apex enters the chain.** -/
theorem exists_mem_growChain (hδ : 0 < δ) (hgeo : IsGeodesicSpace X)
    (hgrow : GrowthStep δ C Rot) {W₀ : Set X}
    (hW₀ : IsWindmill G X δ C Rot W₀) {c₀ : X}
    (hbase : W₀ = Metric.closedBall c₀ (100 * δ)) (c : X) :
    ∃ n : ℕ, c ∈ (growChain hgrow hW₀ n).1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (dist c c₀ / (10 * δ))
  refine ⟨n, closedBall_subset_growChain hδ hgeo hgrow hW₀ hbase n ?_⟩
  refine Metric.mem_closedBall.mpr ?_
  have h10 : (0 : ℝ) < 10 * δ := by linarith
  rw [div_lt_iff₀ h10] at hn
  have h100 : (0 : ℝ) ≤ 100 * δ := by linarith
  linarith

/-! ## The exhaustion -/

/-- **Every element of the rotation closure lies in the group of some
windmill.**

The predicate `∃ n, g ∈ windmillGroup C Rot (chain n)` is closed under the group
operations because the chain is increasing -- `max` for products -- and it holds
on the generators because every apex enters the chain.  `Subgroup.closure_induction`
then covers the whole closure, which is the rotation closure by
`rotationNormalClosure_eq_closure`. -/
theorem exists_isWindmill_mem_windmillGroup (hδ : 0 < δ)
    (hgeo : IsGeodesicSpace X) (hfam : IsRotatingFamily G X C Rot)
    (hgrow : GrowthStep δ C Rot) {W₀ : Set X}
    (hW₀ : IsWindmill G X δ C Rot W₀) {c₀ : X}
    (hbase : W₀ = Metric.closedBall c₀ (100 * δ)) {g : G}
    (hg : g ∈ rotationNormalClosure C Rot) :
    ∃ W : Set X, IsWindmill G X δ C Rot W ∧ g ∈ windmillGroup C Rot W := by
  have hclosure : g ∈ Subgroup.closure {h : G | ∃ c ∈ C, h ∈ Rot c} := by
    rwa [rotationNormalClosure_eq_closure hfam] at hg
  -- `induction` reverts every hypothesis mentioning `g`, so `hg` would land in
  -- the motive and each inductive hypothesis would arrive as an implication
  -- rather than the existential the cases consume.  It has done its work.
  clear hg
  have key : ∃ n : ℕ, g ∈ windmillGroup C Rot (growChain hgrow hW₀ n).1 := by
    induction hclosure using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨c, hc, hxc⟩ := hx
        obtain ⟨n, hn⟩ := exists_mem_growChain hδ hgeo hgrow hW₀ hbase c
        exact ⟨n, mem_windmillGroup hc hn hxc⟩
    | one => exact ⟨0, one_mem _⟩
    | mul x y _ _ ihx ihy =>
        obtain ⟨n, hn⟩ := ihx
        obtain ⟨m, hm⟩ := ihy
        refine ⟨max n m, mul_mem ?_ ?_⟩
        · exact windmillGroup_mono
            (growChain_mono hδ hgrow hW₀ (le_max_left n m)) hn
        · exact windmillGroup_mono
            (growChain_mono hδ hgrow hW₀ (le_max_right n m)) hm
    | inv x _ ihx =>
        obtain ⟨n, hn⟩ := ihx
        exact ⟨n, inv_mem hn⟩
  obtain ⟨n, hn⟩ := key
  exact ⟨(growChain hgrow hW₀ n).1, (growChain hgrow hW₀ n).2, hn⟩

/-- **`WindmillExhaustion`, from the growth step.**

Stated in unfolded form because `GGT/DGOWindmillTheorem53.lean` was being edited
by another session when this was written; both hypothesis and conclusion are
definitionally the named `Prop`s there, so no adapter is needed once the two
files meet. -/
theorem windmillExhaustion_of_growth {ρ : ℝ} (hδ : 0 < δ) (hρ : 200 * δ ≤ ρ)
    (hhyp : IsHyperbolicSpace δ X) (hgeo : IsGeodesicSpace X)
    (hfam : IsRotatingFamily G X C Rot) (hsep : IsSeparated C ρ) {c₀ : X}
    (hc₀ : c₀ ∈ C)
    (hgrow : GrowthStep δ C Rot) :
    ∀ g ∈ rotationNormalClosure C Rot,
      ∃ W : Set X, IsWindmill G X δ C Rot W ∧ g ∈ windmillGroup C Rot W := by
  intro g hg
  exact exists_isWindmill_mem_windmillGroup hδ hgeo hfam hgrow
    (isWindmill_closedBall hδ hρ hhyp hgeo hfam hsep hc₀) rfl hg

end DGOWindmill
end GroupApproximation
