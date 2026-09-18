import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.HKTAffineAction

/-!
# Slices for proper actions of discrete groups

Lane TWWUCT-E (work order WO-TWWUCT-E, `ProperCrossedProduct*`).  Tu (*La conjecture de
Baum--Connes pour les feuilletages moyennables*, K-Theory 17 (1999), Prop. 10.7) and
Higson--Kasparov (Invent. Math. 144 (2001), §9) show that crossed products by proper actions are
`KK`-equivalent to commutative algebras.  The first step of both arguments is geometric: a
proper action of a discrete group has finite stabilizers and admits local *slices*.  Crossed
products over the saturation of a slice are Morita equivalent to crossed products by the finite
stabilizer (Green's imprimitivity theorem).  For the UCT input of
`thm:fixed-radical-membership` in `non_mf_group_notes.tex` the space is `ℝ × H`, where the
affine isometric action acts on the second coordinate (the base of the
Higson--Kasparov--Trout algebra).

This file handles the geometry.

* `DiscreteAction G Z`: a group acting on a topological space by continuous maps.
* `DiscreteAction.IsProper`: every point has a neighbourhood `N` for which only finitely many
  `g` map a point of `N` into `N`.
* `DiscreteAction.stab z`: the stabilizer subgroup, finite for proper actions
  (`finite_stab`).
* `DiscreteAction.exists_slice`: for a proper action on a Hausdorff space, every point `z` has
  arbitrarily small open neighbourhoods `U` that are `Stab(z)`-invariant, such that
  `g • U ∩ U ≠ ∅` implies `g ∈ Stab(z)`.
* `DiscreteAction.inv_mul_mem_stab_of_slice`: translates of a slice meet only along cosets of
  `Stab(z)`.
* `DiscreteAction.exists_countable_slice_cover`: in a second countable space countably many
  slices cover.
* `AffineIsometricAction.toDiscreteAction`, `AffineIsometricAction.lineAction`: the actions on
  `H` and on `ℝ × H`, both proper when the cocycle is metrically proper.
-/

namespace GroupApproximation.Full.TWWUCT

open Topology

universe u v w

/-- A discrete group acting on a topological space by continuous maps. -/
structure DiscreteAction (G : Type u) [Group G] (Z : Type v) [TopologicalSpace Z] where
  /-- The action map. -/
  act : G → Z → Z
  act_one : ∀ z : Z, act 1 z = z
  act_mul : ∀ (g h : G) (z : Z), act (g * h) z = act g (act h z)
  continuous_act : ∀ g : G, Continuous (act g)

namespace DiscreteAction

variable {G : Type u} [Group G] {Z : Type v} [TopologicalSpace Z] (α : DiscreteAction G Z)

theorem act_inv_act (g : G) (z : Z) : α.act g⁻¹ (α.act g z) = z := by
  rw [← α.act_mul, inv_mul_cancel, α.act_one]

theorem act_act_inv (g : G) (z : Z) : α.act g (α.act g⁻¹ z) = z := by
  rw [← α.act_mul, mul_inv_cancel, α.act_one]

/-- The group elements mapping some point of `N` into `N`. -/
def returnSet (N : Set Z) : Set G :=
  {g : G | ∃ x ∈ N, α.act g x ∈ N}

/-- **Properness** for discrete groups: every point has a neighbourhood with finite return
set (Tu 1999, §10; HK 2001, §9). -/
def IsProper : Prop :=
  ∀ z : Z, ∃ N ∈ 𝓝 z, (α.returnSet N).Finite

/-- The stabilizer subgroup of a point. -/
def stab (z : Z) : Subgroup G where
  carrier := {g : G | α.act g z = z}
  mul_mem' := fun {a b} ha hb => by
    have ha' : α.act a z = z := ha
    have hb' : α.act b z = z := hb
    show α.act (a * b) z = z
    rw [α.act_mul, hb', ha']
  one_mem' := α.act_one z
  inv_mem' := fun {a} ha => by
    have ha' : α.act a z = z := ha
    show α.act a⁻¹ z = z
    calc α.act a⁻¹ z = α.act a⁻¹ (α.act a z) := by rw [ha']
      _ = z := α.act_inv_act a z

theorem mem_stab {z : Z} {g : G} : g ∈ α.stab z ↔ α.act g z = z :=
  Iff.rfl

variable {α}

/-- **Stabilizers of proper actions are finite.** -/
theorem finite_stab (hα : α.IsProper) (z : Z) : ((α.stab z : Set G)).Finite := by
  obtain ⟨N, hN, hfin⟩ := hα z
  refine hfin.subset ?_
  intro g hg
  have hg' : α.act g z = z := hg
  have hz : z ∈ N := mem_of_mem_nhds hN
  show ∃ x ∈ N, α.act g x ∈ N
  exact ⟨z, hz, by rw [hg']; exact hz⟩

/-- **Slice theorem for proper actions of discrete groups.**  Every point `z` of a Hausdorff
space with a proper action has, inside any neighbourhood `V`, an open `Stab(z)`-invariant
neighbourhood `U` such that `x ∈ U` and `g • x ∈ U` force `g ∈ Stab(z)`
(Tu 1999, §10; Palais). -/
theorem exists_slice [T2Space Z] (hα : α.IsProper) (z : Z) {V : Set Z} (hV : V ∈ 𝓝 z) :
    ∃ U : Set Z, IsOpen U ∧ z ∈ U ∧ U ⊆ V ∧
      (∀ k ∈ α.stab z, ∀ x ∈ U, α.act k x ∈ U) ∧
      ∀ (g : G) (x : Z), x ∈ U → α.act g x ∈ U → g ∈ α.stab z := by
  obtain ⟨N, hN, hfin⟩ := hα z
  obtain ⟨O, hOsub, hOopen, hzO⟩ := mem_nhds_iff.1 (Filter.inter_mem hN hV)
  have hsep : ∀ g : G, ∃ P Q : Set Z, IsOpen P ∧ IsOpen Q ∧ z ∈ P ∧ α.act g z ∈ Q ∧
      (α.act g z ≠ z → Disjoint P Q) := by
    intro g
    by_cases hg : α.act g z = z
    · exact ⟨Set.univ, Set.univ, isOpen_univ, isOpen_univ, Set.mem_univ _, Set.mem_univ _,
        fun h => absurd hg h⟩
    · obtain ⟨P, Q, hP, hQ, hzP, hgQ, hPQ⟩ := t2_separation (Ne.symm hg)
      exact ⟨P, Q, hP, hQ, hzP, hgQ, fun _ => hPQ⟩
  choose P Q hPo hQo hzP hgQ hPQ using hsep
  obtain ⟨W, hW⟩ : ∃ W : Set Z,
      W = O ∩ ⋂ g ∈ α.returnSet N, (P g ∩ (α.act g) ⁻¹' Q g) := ⟨_, rfl⟩
  have hWopen : IsOpen W := by
    rw [hW]
    exact hOopen.inter (hfin.isOpen_biInter fun g _ =>
      (hPo g).inter ((hQo g).preimage (α.continuous_act g)))
  have hWO : ∀ x ∈ W, x ∈ O := by
    intro x hx
    rw [hW] at hx
    exact hx.1
  have hWP : ∀ x ∈ W, ∀ g ∈ α.returnSet N, x ∈ P g := by
    intro x hx g hg
    rw [hW] at hx
    exact (Set.mem_iInter₂.1 hx.2 g hg).1
  have hWQ : ∀ x ∈ W, ∀ g ∈ α.returnSet N, α.act g x ∈ Q g := by
    intro x hx g hg
    rw [hW] at hx
    exact (Set.mem_iInter₂.1 hx.2 g hg).2
  have hzW : z ∈ W := by
    rw [hW]
    exact ⟨hzO, Set.mem_iInter₂.2 fun g _ => ⟨hzP g, hgQ g⟩⟩
  obtain ⟨U, hU⟩ : ∃ U : Set Z, U = ⋂ k ∈ (α.stab z : Set G), (α.act k) ⁻¹' W := ⟨_, rfl⟩
  have hmemU : ∀ x : Z, x ∈ U ↔ ∀ k ∈ α.stab z, α.act k x ∈ W := by
    intro x
    rw [hU]
    constructor
    · intro hx k hk
      exact Set.mem_iInter₂.1 hx k hk
    · intro hx
      exact Set.mem_iInter₂.2 fun k hk => hx k hk
  have hUW : ∀ x ∈ U, x ∈ W := by
    intro x hx
    have h1 := (hmemU x).1 hx 1 (α.stab z).one_mem
    rw [α.act_one] at h1
    exact h1
  refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hU]
    exact (finite_stab hα z).isOpen_biInter fun k _ => hWopen.preimage (α.continuous_act k)
  · refine (hmemU z).2 fun k hk => ?_
    have hk' : α.act k z = z := hk
    rw [hk']
    exact hzW
  · intro x hx
    exact (hOsub (hWO x (hUW x hx))).2
  · intro k hk x hx
    refine (hmemU (α.act k x)).2 fun f hf => ?_
    rw [← α.act_mul]
    exact (hmemU x).1 hx (f * k) ((α.stab z).mul_mem hf hk)
  · intro g x hx hgx
    by_contra hg
    have hg' : α.act g z ≠ z := hg
    have hxW : x ∈ W := hUW x hx
    have hgxW : α.act g x ∈ W := hUW (α.act g x) hgx
    have hgN : g ∈ α.returnSet N :=
      ⟨x, (hOsub (hWO x hxW)).1, (hOsub (hWO (α.act g x) hgxW)).1⟩
    exact Set.disjoint_left.1 (hPQ g hg') (hWP (α.act g x) hgxW g hgN) (hWQ x hxW g hgN)

/-- **Translates of a slice meet only along cosets of the stabilizer**: if `g • x = h • y` with
`x, y ∈ U`, then `h⁻¹ g ∈ Stab(z)`. -/
theorem inv_mul_mem_stab_of_slice {z : Z} {U : Set Z}
    (hret : ∀ (g : G) (x : Z), x ∈ U → α.act g x ∈ U → g ∈ α.stab z)
    {g h : G} {x y : Z} (hx : x ∈ U) (hy : y ∈ U) (hxy : α.act g x = α.act h y) :
    h⁻¹ * g ∈ α.stab z := by
  refine hret (h⁻¹ * g) x hx ?_
  rw [α.act_mul, hxy, α.act_inv_act]
  exact hy

/-- Conversely, stabilizer elements move a slice into itself, so `g • U = h • U` along a coset:
`g • x ∈ h • U` whenever `h⁻¹ g ∈ Stab(z)`. -/
theorem act_mem_translate_of_inv_mul_mem_stab {z : Z} {U : Set Z}
    (hinv : ∀ k ∈ α.stab z, ∀ x ∈ U, α.act k x ∈ U)
    {g h : G} (hgh : h⁻¹ * g ∈ α.stab z) {x : Z} (hx : x ∈ U) :
    ∃ y ∈ U, α.act g x = α.act h y := by
  refine ⟨α.act (h⁻¹ * g) x, hinv (h⁻¹ * g) hgh x hx, ?_⟩
  rw [α.act_mul, α.act_act_inv]

/-- **Countable slice covers**: in a second countable Hausdorff space with a proper action there
are slices `U z` at every point, countably many of which cover the space. -/
theorem exists_countable_slice_cover [T2Space Z] [SecondCountableTopology Z]
    (hα : α.IsProper) :
    ∃ (U : Z → Set Z) (T : Set Z), T.Countable ∧ (⋃ z ∈ T, U z) = Set.univ ∧
      ∀ z : Z, IsOpen (U z) ∧ z ∈ U z ∧ (∀ k ∈ α.stab z, ∀ x ∈ U z, α.act k x ∈ U z) ∧
        ∀ (g : G) (x : Z), x ∈ U z → α.act g x ∈ U z → g ∈ α.stab z := by
  have hsl : ∀ z : Z, ∃ U : Set Z, IsOpen U ∧ z ∈ U ∧
      (∀ k ∈ α.stab z, ∀ x ∈ U, α.act k x ∈ U) ∧
      ∀ (g : G) (x : Z), x ∈ U → α.act g x ∈ U → g ∈ α.stab z := by
    intro z
    obtain ⟨U, hUo, hzU, _, hinv, hret⟩ := exists_slice hα z Filter.univ_mem
    exact ⟨U, hUo, hzU, hinv, hret⟩
  choose U hUo hzU hinv hret using hsl
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
  refine ⟨U, T, hT, ?_, fun z => ⟨hUo z, hzU z, hinv z, hret z⟩⟩
  rw [hTU]
  exact Set.eq_univ_of_forall fun z => Set.mem_iUnion.2 ⟨z, hzU z⟩

end DiscreteAction

namespace AffineIsometricAction

variable {G : Type u} [Group G] {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (b : AffineIsometricAction G H)

/-- The affine isometric action as a `DiscreteAction` on `H`. -/
def toDiscreteAction : DiscreteAction G H where
  act := b.act
  act_one := b.act_one
  act_mul := b.act_mul
  continuous_act := b.continuous_act

/-- The action `(t, h) ↦ (t, g • h)` on `ℝ × H`, the base of the Higson--Kasparov--Trout
algebra. -/
def lineAction : DiscreteAction G (ℝ × H) where
  act g x := (x.1, b.act g x.2)
  act_one x := Prod.ext rfl (b.act_one x.2)
  act_mul g h x := Prod.ext rfl (b.act_mul g h x.2)
  continuous_act g := continuous_fst.prodMk ((b.continuous_act g).comp continuous_snd)

theorem lineAction_act (g : G) (x : ℝ × H) : b.lineAction.act g x = (x.1, b.act g x.2) :=
  rfl

theorem norm_le_of_mem_ball_one {z x : H} (hx : x ∈ Metric.ball z 1) : ‖x‖ ≤ ‖z‖ + 1 := by
  have h1 : dist x z < 1 := Metric.mem_ball.1 hx
  have h2 : dist x 0 ≤ dist x z + dist z 0 := dist_triangle x z 0
  rw [dist_zero_right, dist_zero_right] at h2
  linarith

variable {b}

/-- **A metrically proper affine isometric action is proper** on `H`. -/
theorem isProper_toDiscreteAction (hb : b.IsMetricallyProper) : b.toDiscreteAction.IsProper := by
  intro z
  refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z one_pos, ?_⟩
  refine (b.finite_bounded_return hb (‖z‖ + 1)).subset ?_
  rintro g ⟨x, hx, hgx⟩
  exact ⟨x, norm_le_of_mem_ball_one hx, norm_le_of_mem_ball_one hgx⟩

theorem mem_ball_snd {z x : ℝ × H} (hx : x ∈ Metric.ball z 1) : x.2 ∈ Metric.ball z.2 1 := by
  have h1 : dist x z < 1 := Metric.mem_ball.1 hx
  have h2 : dist x.2 z.2 ≤ dist x z := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  exact Metric.mem_ball.2 (lt_of_le_of_lt h2 h1)

/-- **A metrically proper affine isometric action is proper on `ℝ × H`** (HKT 1998, §4;
HK 2001, §9, for the base of `A(H)`). -/
theorem isProper_lineAction (hb : b.IsMetricallyProper) : b.lineAction.IsProper := by
  intro z
  refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z one_pos, ?_⟩
  refine (b.finite_bounded_return hb (‖z.2‖ + 1)).subset ?_
  rintro g ⟨x, hx, hgx⟩
  exact ⟨x.2, norm_le_of_mem_ball_one (mem_ball_snd hx),
    norm_le_of_mem_ball_one (mem_ball_snd hgx)⟩

/-- The stabilizer of `(t, h)` for the action on `ℝ × H` is the stabilizer of `h`. -/
theorem mem_stab_lineAction {g : G} {x : ℝ × H} :
    g ∈ b.lineAction.stab x ↔ g ∈ b.toDiscreteAction.stab x.2 := by
  constructor
  · intro hg
    have hg' : (x.1, b.act g x.2) = x := hg
    show b.act g x.2 = x.2
    exact congrArg Prod.snd hg'
  · intro hg
    have hg' : b.act g x.2 = x.2 := hg
    show (x.1, b.act g x.2) = x
    exact Prod.ext rfl hg'

end AffineIsometricAction

end GroupApproximation.Full.TWWUCT
