import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.StabQComplexStabRankBasic
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.StabQComplexAdditive
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.LocallyConstant.Basic

/-!
# The rank of projections in `𝒦 = Stab ℂ`

For `p ∈ 𝒦` let `V p = {y ∈ 𝒦 | p y = y, y e₀₀ = y}`, the columns in the range of `p`.
These form a finite-dimensional subspace, and the **rank** of `p` is its dimension
(Blackadar, *K-Theory for Operator Algebras*, 4.2 and 5.1):

* `V p` is finite-dimensional: if `‖p - a‖ < 1` with `a` an `N × N` matrix, then `y ↦ a y`
  embeds `V p` into the span `D N` of the columns `E i 0`, `i < N`;
* for a projection `q` with `‖p - q‖ < 1`, `y ↦ q y` embeds `V p` into `V q`, so the rank is
  locally constant, hence constant along projection paths;
* for orthogonal projections `V (p + q) = V p ⊕ V q`;
* `V (e₀₀) = ℂ e₀₀`, so the rank of `corner ℂ 1` is `1`.

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(lane TWWKK-C1, work order WO-TWWKK-C1).
-/

namespace GroupApproximation.Full.TWWKK

noncomputable section

namespace StabRankAux

open Stab

/-! ## Spans of columns -/

/-- The span of the columns `E i 0` with `i < N`. -/
def D (N : ℕ) : Submodule ℂ (Ambient ℂ) :=
  Submodule.span ℂ (Set.range fun i : Fin N => E (i : ℕ) 0)

instance instFiniteDimensionalD (N : ℕ) : FiniteDimensional ℂ (D N) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

theorem E_mem_D {N i : ℕ} (hi : i < N) : E i 0 ∈ D N :=
  Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩

/-- An `N × N` matrix times a column is a combination of the first `N` columns. -/
theorem C_mul_col_mem {N : ℕ} {a y : Ambient ℂ} (ha : a ∈ C N) (hy : y ∈ closedSubalgebra ℂ)
    (hye : y * E 0 0 = y) : a * y ∈ D N := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, j, hi, _, rfl⟩ := hx
    rw [E_mul_col i j hy hye]
    exact Submodule.smul_mem _ _ (E_mem_D hi)
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/-! ## The column space of an element -/

/-- The columns in the range of `p`: `V p = {y ∈ 𝒦 | p y = y, y e₀₀ = y}`. -/
def V (p : Stab ℂ) : Submodule ℂ (Ambient ℂ) where
  carrier := {y | y ∈ closedSubalgebra ℂ ∧ (p : Ambient ℂ) * y = y ∧ y * E 0 0 = y}
  add_mem' := by
    rintro y z ⟨hy, hpy, hye⟩ ⟨hz, hpz, hze⟩
    exact ⟨add_mem hy hz, by rw [mul_add, hpy, hpz], by rw [add_mul, hye, hze]⟩
  zero_mem' := ⟨zero_mem _, mul_zero _, zero_mul _⟩
  smul_mem' := by
    rintro c y ⟨hy, hpy, hye⟩
    exact ⟨SMulMemClass.smul_mem c hy, by rw [mul_smul_comm, hpy], by rw [smul_mul_assoc, hye]⟩

theorem mem_V {p : Stab ℂ} {y : Ambient ℂ} :
    y ∈ V p ↔ y ∈ closedSubalgebra ℂ ∧ (p : Ambient ℂ) * y = y ∧ y * E 0 0 = y :=
  Iff.rfl

theorem coe_mul_self {p : Stab ℂ} (hp : IsStarProjection p) : (p : Ambient ℂ) * p = p := by
  have h : p * p = p := hp.isIdempotentElem
  exact congrArg Subtype.val h

theorem coe_star {p : Stab ℂ} (hp : IsStarProjection p) : star (p : Ambient ℂ) = p := by
  have h : star p = p := hp.isSelfAdjoint
  exact congrArg Subtype.val h

theorem mul_mem_V {q : Stab ℂ} (hqq : (q : Ambient ℂ) * q = q) {y : Ambient ℂ}
    (hy : y ∈ closedSubalgebra ℂ) (hye : y * E 0 0 = y) : (q : Ambient ℂ) * y ∈ V q :=
  mem_V.mpr ⟨mul_mem q.2 hy, by rw [← mul_assoc, hqq], by rw [mul_assoc, hye]⟩

/-- A vector fixed by an operator of norm `< 1` vanishes. -/
theorem eq_zero_of_norm_lt {u y : Ambient ℂ} (hu : ‖u‖ < 1) (h : u * y = y) : y = 0 := by
  have h1 : ‖y‖ ≤ ‖u‖ * ‖y‖ := by
    calc ‖y‖ = ‖u * y‖ := by rw [h]
      _ ≤ ‖u‖ * ‖y‖ := norm_mul_le u y
  have h2 : ‖y‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hne)
    have h3 : ‖u‖ * ‖y‖ < 1 * ‖y‖ := mul_lt_mul_of_pos_right hu hpos
    linarith
  exact norm_eq_zero.mp h2

/-- **`V p` is finite-dimensional**: it embeds into `D N` for an `N × N` matrix near `p`. -/
instance instFiniteDimensionalV (p : Stab ℂ) : FiniteDimensional ℂ (V p) := by
  have hp : (p : Ambient ℂ) ∈ closure (finiteMatrices ℂ : Set (Ambient ℂ)) := p.2
  obtain ⟨a, ha, hpa⟩ := Metric.mem_closure_iff.mp hp 1 one_pos
  obtain ⟨N, hN⟩ := exists_C ha
  let f : V p →ₗ[ℂ] D N :=
    { toFun := fun y => ⟨a * y, C_mul_col_mem hN (mem_V.mp y.2).1 (mem_V.mp y.2).2.2⟩
      map_add' := fun y z => Subtype.ext (mul_add a y z)
      map_smul' := fun c y => Subtype.ext (mul_smul_comm c a y) }
  refine FiniteDimensional.of_injective f ((injective_iff_map_eq_zero f).mpr ?_)
  intro y hy
  have hy0 : a * (y : Ambient ℂ) = 0 := congrArg Subtype.val hy
  have hpy : (p : Ambient ℂ) * y = y := (mem_V.mp y.2).2.1
  have hu : ‖(p : Ambient ℂ) - a‖ < 1 := by
    rw [← dist_eq_norm]
    exact hpa
  have h1 : ((p : Ambient ℂ) - a) * y = y := by
    rw [sub_mul, hpy, hy0, sub_zero]
  exact Subtype.ext (eq_zero_of_norm_lt hu h1)

/-- The rank of `p ∈ 𝒦`: the dimension of its column space. -/
def stabRankFun (p : Stab ℂ) : ℕ :=
  Module.finrank ℂ (V p)

/-! ## Invariance along paths -/

/-- If `q` is a projection with `‖p - q‖ < 1` then `rank p ≤ rank q`. -/
theorem stabRankFun_le {p q : Stab ℂ} (hq : IsStarProjection q)
    (hpq : ‖(p : Ambient ℂ) - q‖ < 1) : stabRankFun p ≤ stabRankFun q := by
  have hqq := coe_mul_self hq
  let f : V p →ₗ[ℂ] V q :=
    { toFun := fun y => ⟨(q : Ambient ℂ) * y,
        mul_mem_V hqq (mem_V.mp y.2).1 (mem_V.mp y.2).2.2⟩
      map_add' := fun y z => Subtype.ext (mul_add (q : Ambient ℂ) y z)
      map_smul' := fun c y => Subtype.ext (mul_smul_comm c (q : Ambient ℂ) y) }
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).mpr ?_
    intro y hy
    have hy0 : (q : Ambient ℂ) * y = 0 := congrArg Subtype.val hy
    have hpy : (p : Ambient ℂ) * y = y := (mem_V.mp y.2).2.1
    have h1 : ((p : Ambient ℂ) - q) * y = y := by
      rw [sub_mul, hpy, hy0, sub_zero]
    exact Subtype.ext (eq_zero_of_norm_lt hpq h1)
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-- The rank is constant along projection paths. -/
theorem stabRankFun_path {p q : Stab ℂ} (h : ProjectionPath p q) :
    stabRankFun p = stabRankFun q := by
  obtain ⟨P, hP, hproj, h0, h1⟩ := h
  have hloc : IsLocallyConstant fun t => stabRankFun (P t) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t
    have hev : ∀ᶠ s in nhds t, dist (P s) (P t) < 1 :=
      Metric.tendsto_nhds.mp (hP.tendsto t) 1 one_pos
    filter_upwards [hev] with s hs
    have hn : ‖((P s : Stab ℂ) : Ambient ℂ) - P t‖ < 1 := by
      rw [← dist_eq_norm]
      exact hs
    have hn' : ‖((P t : Stab ℂ) : Ambient ℂ) - P s‖ < 1 := by
      rw [← dist_eq_norm, dist_comm]
      exact hs
    exact le_antisymm (stabRankFun_le (hproj t) hn) (stabRankFun_le (hproj s) hn')
  calc stabRankFun p = stabRankFun (P 0) := by rw [h0]
    _ = stabRankFun (P 1) := hloc.apply_eq_of_preconnectedSpace 0 1
    _ = stabRankFun q := by rw [h1]

/-! ## Additivity -/

/-- The rank is additive on orthogonal projections. -/
theorem stabRankFun_add {p q : Stab ℂ} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : p * q = 0) : stabRankFun (p + q) = stabRankFun p + stabRankFun q := by
  have hpp := coe_mul_self hp
  have hqq := coe_mul_self hq
  have hpq' : (p : Ambient ℂ) * q = 0 := congrArg Subtype.val hpq
  have hqp' : (q : Ambient ℂ) * p = 0 := by
    rw [← coe_star hq, ← coe_star hp, ← star_mul, hpq', star_zero]
  have hinf : V p ⊓ V q = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.mp hy
    have hpy : (p : Ambient ℂ) * y = y := (mem_V.mp hy1).2.1
    have hqy : (q : Ambient ℂ) * y = y := (mem_V.mp hy2).2.1
    rw [Submodule.mem_bot]
    calc y = (p : Ambient ℂ) * ((q : Ambient ℂ) * y) := by rw [hqy, hpy]
      _ = 0 := by rw [← mul_assoc, hpq', zero_mul]
  have hsup : V (p + q) = V p ⊔ V q := by
    apply le_antisymm
    · intro y hy
      obtain ⟨hy0, hpqy, hye⟩ := mem_V.mp hy
      have hsum : (p : Ambient ℂ) * y + (q : Ambient ℂ) * y = y := by
        rw [← add_mul]
        exact hpqy
      rw [← hsum]
      exact Submodule.add_mem_sup (mul_mem_V hpp hy0 hye) (mul_mem_V hqq hy0 hye)
    · refine sup_le ?_ ?_
      · intro y hy
        obtain ⟨hy0, hpy, hye⟩ := mem_V.mp hy
        have h0 : (q : Ambient ℂ) * y = 0 := by
          rw [← hpy, ← mul_assoc, hqp', zero_mul]
        refine mem_V.mpr ⟨hy0, ?_, hye⟩
        show ((p : Ambient ℂ) + q) * y = y
        rw [add_mul, hpy, h0, add_zero]
      · intro y hy
        obtain ⟨hy0, hqy, hye⟩ := mem_V.mp hy
        have h0 : (p : Ambient ℂ) * y = 0 := by
          rw [← hqy, ← mul_assoc, hpq', zero_mul]
        refine mem_V.mpr ⟨hy0, ?_, hye⟩
        show ((p : Ambient ℂ) + q) * y = y
        rw [add_mul, hqy, h0, zero_add]
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq (V p) (V q)
  rw [hinf, finrank_bot, add_zero, ← hsup] at hfin
  exact hfin

/-! ## The corner projection -/

theorem coe_corner_one : ((Stab.corner ℂ (1 : ℂ) : Stab ℂ) : Ambient ℂ) = E 0 0 :=
  rfl

theorem V_corner : V (Stab.corner ℂ (1 : ℂ)) = ℂ ∙ E 0 0 := by
  apply le_antisymm
  · intro y hy
    obtain ⟨hy0, hly, hye⟩ := mem_V.mp hy
    rw [coe_corner_one] at hly
    rw [Submodule.mem_span_singleton]
    refine ⟨vst y, ?_⟩
    rw [← compress hy0, hly, hye]
  · rw [Submodule.span_singleton_le_iff_mem, mem_V, coe_corner_one]
    exact ⟨E_mem 0 0, E_mul_self 0 0 0, E_mul_self 0 0 0⟩

end StabRankAux

open StabRankAux in
/-- **The rank on projections of `𝒦 = Stab ℂ`** (Blackadar 4.2, 5.1): the dimension of the
column space, constant along projection paths and additive on orthogonal projections. -/
noncomputable def stabRank : ProjectionRank (Stab ℂ) where
  toFun := stabRankFun
  path_eq := stabRankFun_path
  add_eq := stabRankFun_add

/-- The rank of the corner projection `e₀₀ = corner ℂ 1` is `1`. -/
theorem stabRank_corner_one : stabRank.toFun (Stab.corner ℂ (1 : ℂ)) = 1 := by
  show Module.finrank ℂ (StabRankAux.V (Stab.corner ℂ (1 : ℂ))) = 1
  rw [StabRankAux.V_corner]
  exact finrank_span_singleton StabRankAux.E00_ne

end

end GroupApproximation.Full.TWWKK
