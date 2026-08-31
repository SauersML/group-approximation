import GroupApproximation.Topology.TautologicalCommonZero
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Homotopy.Lifting

/-!
# The rank-one common-zero theorem, by winding number

`GroupApproximation.Topology.TautologicalCommonZero` reduces the topological
input of the STW Problem XXII counterexample to `CommonZeroProperty`: over
`ℂPᴺ`, a section of a sum of at most `N` copies of the tautological line bundle
has a zero.  The printed proof is the top Chern class of `L^{⊕k}`, which Mathlib
cannot express.  This file proves the case `k = 1` -- a *single* copy of `L`,
over `ℂPᴺ` for every `N ≥ 1` -- with no characteristic classes at all.

## The argument

Suppose `g` is continuous, nowhere zero on `ℂ^{N+1} ∖ {0}` and homogeneous of
degree `-1`.  Because `N ≥ 1` there is a second coordinate direction, and

```text
fill σ r = κ(σ,r) • e₀ + (1 - ‖κ(σ,r)‖) • e₁,      κ(σ,r) = (1-σ)·e^{2πir} + σ
```

is a continuous square of *nonzero* vectors: the second summand rescues the one
point where `κ` vanishes.  Its `σ = 0` edge is the circle orbit `e^{2πir} • e₀`
and its three other edges are constantly `e₀`, because `‖κ‖ = 1` there.  So
`g ∘ fill` is a homotopy, relative to `{0,1}`, from the loop
`r ↦ (e^{2πir})⁻¹ · g e₀` to the constant loop at `g e₀`, inside `ℂ ∖ {0}`.

`Complex.exp : ℂ → ℂ ∖ {0}` is a covering map, homotopic-rel-endpoints loops
lift to paths with the same endpoint, and the first loop lifts explicitly to
`t ↦ log (g e₀) - 2πit` while the constant loop lifts to a constant.  Comparing
endpoints gives `2πi = 0`.

Everything here is a theorem; nothing is assumed.

## Main results

* `no_winding_square` -- the covering-space core, stated for an arbitrary
  square in `ℂ ∖ {0}` so that the geometry and the homotopy theory stay apart.
* `not_nonvanishing_homogeneous` -- no nowhere-vanishing degree `-1`
  homogeneous scalar function on `ℂ^{N+1} ∖ {0}` when `N ≥ 1`.
* `exists_zero_of_subsingleton`, `hasCommonZero_of_subsingleton` -- the
  rank-one fragment of `TautologicalCommonZero.CommonZeroProperty`.

The general `CommonZeroProperty` (rank up to `N`) is *not* proved here and is
not available from Mathlib; see the residue note in the module docstring of
`TautologicalCommonZero`.
-/

namespace GroupApproximation
namespace TautologicalLineWinding

open TautologicalCommonZero

noncomputable section

/-! ### The circle -/

/-- `circleLoop r = exp (2π i r)`. -/
def circleLoop (r : ℝ) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * r) : ℂ) * Complex.I)

theorem circleLoop_ne_zero (r : ℝ) : circleLoop r ≠ 0 := Complex.exp_ne_zero _

theorem norm_circleLoop (r : ℝ) : ‖circleLoop r‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem circleLoop_zero : circleLoop 0 = 1 := by
  have h : (↑(2 * Real.pi * 0) : ℂ) * Complex.I = 0 := by simp
  rw [circleLoop, h, Complex.exp_zero]

theorem circleLoop_one : circleLoop 1 = 1 := by
  have h : (↑(2 * Real.pi * 1) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [circleLoop, h, Complex.exp_two_pi_mul_I]

theorem continuous_circleLoop : Continuous circleLoop := by
  have h0 : Continuous fun r : ℝ => 2 * Real.pi * r := by fun_prop
  have h1 : Continuous fun r : ℝ => (↑(2 * Real.pi * r) : ℂ) * Complex.I :=
    (Complex.continuous_ofReal.comp' h0).mul continuous_const
  exact h1.cexp

/-! ### The square that fills the tautological circle -/

/-- The straight-line contraction of the unit circle to the point `1` inside
the closed unit disc. -/
def kap (σ r : ℝ) : ℂ := (1 - (σ : ℂ)) * circleLoop r + (σ : ℂ)

theorem kap_zero_left (r : ℝ) : kap 0 r = circleLoop r := by simp [kap]

theorem kap_one_left (r : ℝ) : kap 1 r = 1 := by simp [kap]

theorem kap_zero_right (σ : ℝ) : kap σ 0 = 1 := by
  rw [kap, circleLoop_zero]; ring

theorem kap_one_right (σ : ℝ) : kap σ 1 = 1 := by
  rw [kap, circleLoop_one]; ring

theorem norm_kap_zero_left (r : ℝ) : ‖kap 0 r‖ = 1 := by
  rw [kap_zero_left, norm_circleLoop]

theorem norm_kap_one_left (r : ℝ) : ‖kap 1 r‖ = 1 := by
  rw [kap_one_left, norm_one]

theorem norm_kap_zero_right (σ : ℝ) : ‖kap σ 0‖ = 1 := by
  rw [kap_zero_right, norm_one]

theorem norm_kap_one_right (σ : ℝ) : ‖kap σ 1‖ = 1 := by
  rw [kap_one_right, norm_one]

theorem continuous_kap : Continuous fun p : ℝ × ℝ => kap p.1 p.2 := by
  have h1 : Continuous fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp' continuous_fst
  have h2 : Continuous fun p : ℝ × ℝ => circleLoop p.2 :=
    continuous_circleLoop.comp' continuous_snd
  exact ((continuous_const.sub h1).mul h2).add h1

/-- The first coordinate vector `e₀ = (1,0,…,0)` of `ℂ^{N+1}`. -/
def basePoint (N : ℕ) : Fin (N + 1) → ℂ := Pi.single 0 1

theorem basePoint_ne_zero (N : ℕ) : basePoint N ≠ 0 := by
  intro h
  have hz := congrFun h (0 : Fin (N + 1))
  rw [basePoint, Pi.single_eq_same, Pi.zero_apply] at hz
  exact one_ne_zero hz

/-- A continuous square of *nonzero* vectors in `ℂ^{N+1}` whose `σ = 0` edge is
the circle orbit `circleLoop r • e₀` and whose three other edges are constantly
`e₀`.  The second summand is nonzero exactly where `κ` vanishes, which is what
makes the whole square avoid the origin. -/
def fill (N : ℕ) (i₁ : Fin (N + 1)) (σ r : ℝ) : Fin (N + 1) → ℂ :=
  kap σ r • basePoint N +
    ((↑(1 - ‖kap σ r‖) : ℂ)) • (Pi.single i₁ 1 : Fin (N + 1) → ℂ)

theorem fill_apply_zero (N : ℕ) (i₁ : Fin (N + 1)) (h₁ : i₁ ≠ 0) (σ r : ℝ) :
    fill N i₁ σ r 0 = kap σ r := by
  rw [fill]
  simp [basePoint, Pi.single_eq_of_ne (Ne.symm h₁)]

theorem fill_apply_side (N : ℕ) (i₁ : Fin (N + 1)) (h₁ : i₁ ≠ 0) (σ r : ℝ) :
    fill N i₁ σ r i₁ = ((↑(1 - ‖kap σ r‖) : ℂ)) := by
  rw [fill]
  simp [basePoint, Pi.single_eq_of_ne h₁]

theorem fill_ne_zero (N : ℕ) (i₁ : Fin (N + 1)) (h₁ : i₁ ≠ 0) (σ r : ℝ) :
    fill N i₁ σ r ≠ 0 := by
  by_cases hk : kap σ r = 0
  · intro h
    have hv := congrFun h i₁
    rw [fill_apply_side N i₁ h₁ σ r, Pi.zero_apply] at hv
    simp [hk] at hv
  · intro h
    have hv := congrFun h (0 : Fin (N + 1))
    rw [fill_apply_zero N i₁ h₁ σ r, Pi.zero_apply] at hv
    exact hk hv

theorem fill_of_norm_kap_eq_one (N : ℕ) (i₁ : Fin (N + 1)) (σ r : ℝ)
    (h : ‖kap σ r‖ = 1) : fill N i₁ σ r = kap σ r • basePoint N := by
  rw [fill, h]
  simp

theorem fill_zero_left (N : ℕ) (i₁ : Fin (N + 1)) (r : ℝ) :
    fill N i₁ 0 r = circleLoop r • basePoint N := by
  rw [fill_of_norm_kap_eq_one N i₁ 0 r (norm_kap_zero_left r), kap_zero_left]

theorem fill_one_left (N : ℕ) (i₁ : Fin (N + 1)) (r : ℝ) :
    fill N i₁ 1 r = basePoint N := by
  rw [fill_of_norm_kap_eq_one N i₁ 1 r (norm_kap_one_left r), kap_one_left, one_smul]

theorem fill_zero_right (N : ℕ) (i₁ : Fin (N + 1)) (σ : ℝ) :
    fill N i₁ σ 0 = basePoint N := by
  rw [fill_of_norm_kap_eq_one N i₁ σ 0 (norm_kap_zero_right σ), kap_zero_right, one_smul]

theorem fill_one_right (N : ℕ) (i₁ : Fin (N + 1)) (σ : ℝ) :
    fill N i₁ σ 1 = basePoint N := by
  rw [fill_of_norm_kap_eq_one N i₁ σ 1 (norm_kap_one_right σ), kap_one_right, one_smul]

theorem continuous_fill (N : ℕ) (i₁ : Fin (N + 1)) :
    Continuous fun p : ℝ × ℝ => fill N i₁ p.1 p.2 := by
  have hk : Continuous fun p : ℝ × ℝ => kap p.1 p.2 := continuous_kap
  have hn : Continuous fun p : ℝ × ℝ => ((↑(1 - ‖kap p.1 p.2‖) : ℂ)) :=
    Complex.continuous_ofReal.comp' (continuous_const.sub hk.norm)
  exact (hk.smul continuous_const).add (hn.smul continuous_const)

/-! ### The covering-space core -/

/-- **No winding square.**  A continuous square in `ℂ ∖ {0}` cannot be constant
equal to `c` on three of its sides while running once around the origin,
`t ↦ (e^{2πit})⁻¹ · c`, on the fourth.

This is the only place where algebraic topology enters; it is the statement
that the loop `t ↦ e^{-2πit}` is not null-homotopic in `ℂ ∖ {0}`, proved
through the covering map `Complex.exp`. -/
theorem no_winding_square (c : ℂ) (hc : c ≠ 0)
    (Φ : unitInterval × unitInterval → ℂ)
    (hΦ : Continuous Φ)
    (hne : ∀ p, Φ p ≠ 0)
    (hleft : ∀ t : unitInterval, Φ (0, t) = (circleLoop (t : ℝ))⁻¹ * c)
    (hright : ∀ t : unitInterval, Φ (1, t) = c)
    (hbot : ∀ s : unitInterval, Φ (s, 0) = c)
    (htop : ∀ s : unitInterval, Φ (s, 1) = c) : False := by
  have cov := Complex.isCoveringMap_exp
  have hlog : Complex.exp (Complex.log c) = c := Complex.exp_log hc
  -- the two loops in `ℂ ∖ {0}`
  have hγ₀ : Continuous fun t : unitInterval =>
      (⟨Φ (0, t), hne (0, t)⟩ : {w : ℂ // w ≠ 0}) :=
    Continuous.subtype_mk (hΦ.comp' (continuous_const.prodMk continuous_id))
      (fun t => hne (0, t))
  let γ₀ : C(unitInterval, {w : ℂ // w ≠ 0}) :=
    ⟨fun t => ⟨Φ (0, t), hne (0, t)⟩, hγ₀⟩
  let γ₁ : C(unitInterval, {w : ℂ // w ≠ 0}) :=
    ContinuousMap.const unitInterval ⟨c, hc⟩
  -- the square is a homotopy rel `{0,1}` between them
  have hrel : γ₀.HomotopicRel γ₁ ({0, 1} : Set unitInterval) := by
    refine ⟨{ toFun := fun p => ⟨Φ p, hne p⟩
              continuous_toFun := Continuous.subtype_mk hΦ hne
              map_zero_left := fun _ => rfl
              map_one_left := fun t => Subtype.ext (hright t)
              prop' := ?_ }⟩
    intro s x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · apply Subtype.ext
      show Φ (s, (0 : unitInterval)) = Φ ((0 : unitInterval), (0 : unitInterval))
      exact (hbot s).trans (hbot 0).symm
    · apply Subtype.ext
      show Φ (s, (1 : unitInterval)) = Φ ((0 : unitInterval), (1 : unitInterval))
      exact (htop s).trans (htop 0).symm
  -- both loops start at `exp (log c)`
  have h₀ : γ₀ 0 =
      (⟨Complex.exp (Complex.log c), Complex.exp_ne_zero _⟩ : {w : ℂ // w ≠ 0}) := by
    apply Subtype.ext
    show Φ ((0 : unitInterval), (0 : unitInterval)) = Complex.exp (Complex.log c)
    rw [hlog]
    exact hbot 0
  have h₁ : γ₁ 0 =
      (⟨Complex.exp (Complex.log c), Complex.exp_ne_zero _⟩ : {w : ℂ // w ≠ 0}) := by
    apply Subtype.ext
    show c = Complex.exp (Complex.log c)
    rw [hlog]
  have key := cov.liftPath_apply_one_eq_of_homotopicRel hrel (Complex.log c) h₀ h₁
  -- the constant loop lifts to a constant path
  have hR : (ContinuousMap.const unitInterval (Complex.log c)) =
      cov.liftPath γ₁ (Complex.log c) h₁ :=
    (cov.eq_liftPath_iff' h₁).mpr ⟨funext fun _ => Subtype.ext hlog, rfl⟩
  have hR1 : cov.liftPath γ₁ (Complex.log c) h₁ 1 = Complex.log c :=
    congrArg (fun f : C(unitInterval, ℂ) => f 1) hR.symm
  -- the winding loop lifts to the explicit path `t ↦ log c - 2πit`
  have h0 : Continuous fun t : unitInterval => 2 * Real.pi * (t : ℝ) :=
    continuous_const.mul continuous_subtype_val
  have hΓcont : Continuous fun t : unitInterval =>
      Complex.log c - (↑(2 * Real.pi * (t : ℝ)) : ℂ) * Complex.I :=
    continuous_const.sub ((Complex.continuous_ofReal.comp' h0).mul continuous_const)
  let Γ : C(unitInterval, ℂ) :=
    ⟨fun t => Complex.log c - (↑(2 * Real.pi * (t : ℝ)) : ℂ) * Complex.I, hΓcont⟩
  have hL : Γ = cov.liftPath γ₀ (Complex.log c) h₀ := by
    refine (cov.eq_liftPath_iff' h₀).mpr ⟨funext fun t => ?_, ?_⟩
    · apply Subtype.ext
      show Complex.exp (Complex.log c - (↑(2 * Real.pi * (t : ℝ)) : ℂ) * Complex.I)
          = Φ ((0 : unitInterval), t)
      rw [hleft t, Complex.exp_sub, hlog, circleLoop]
      ring
    · show Complex.log c - (↑(2 * Real.pi * (0 : ℝ)) : ℂ) * Complex.I = Complex.log c
      simp
  -- compare the two endpoints
  have hend : Γ 1 = cov.liftPath γ₀ (Complex.log c) h₀ 1 :=
    congrArg (fun f : C(unitInterval, ℂ) => f 1) hL
  rw [key, hR1] at hend
  have e1 : Complex.log c - (↑(2 * Real.pi * (1 : ℝ)) : ℂ) * Complex.I = Complex.log c := hend
  have e2 : (2 : ℂ) * (Real.pi : ℂ) * Complex.I = 0 := by
    have h := sub_eq_self.mp e1
    have hcast : (↑(2 * Real.pi * (1 : ℝ)) : ℂ) * Complex.I
        = (2 : ℂ) * (Real.pi : ℂ) * Complex.I := by push_cast; ring
    rw [hcast] at h
    exact h
  exact Complex.two_pi_I_ne_zero e2

/-! ### The rank-one common-zero theorem -/

/-- **The rank-one obstruction.**  For `N ≥ 1` there is no continuous,
nowhere-vanishing function on `ℂ^{N+1} ∖ {0}` which is homogeneous of degree
`-1`; equivalently, every continuous section of the tautological line bundle
over `ℂPᴺ` has a zero. -/
theorem not_nonvanishing_homogeneous {N : ℕ} (hN : 1 ≤ N)
    (g : (Fin (N + 1) → ℂ) → ℂ)
    (hcont : ContinuousOn g (punctured N))
    (hhom : ∀ (c : ℂ) (z : Fin (N + 1) → ℂ), c ≠ 0 → z ≠ 0 → g (c • z) = c⁻¹ * g z)
    (hne : ∀ z : Fin (N + 1) → ℂ, z ≠ 0 → g z ≠ 0) : False := by
  obtain ⟨i₁, h₁⟩ : ∃ i : Fin (N + 1), i ≠ 0 := by
    refine ⟨⟨1, by omega⟩, fun h => ?_⟩
    -- `Fin.val_zero` is `rfl`, so both sides reduce to numerals.
    have hv : (1 : ℕ) = 0 := congrArg Fin.val h
    exact Nat.one_ne_zero hv
  have hbase : basePoint N ≠ 0 := basePoint_ne_zero N
  have hcne : g (basePoint N) ≠ 0 := hne _ hbase
  have hcf : Continuous fun p : unitInterval × unitInterval =>
      fill N i₁ (p.1 : ℝ) (p.2 : ℝ) :=
    (continuous_fill N i₁).comp'
      ((continuous_subtype_val.comp' continuous_fst).prodMk
        (continuous_subtype_val.comp' continuous_snd))
  have hmem : ∀ p : unitInterval × unitInterval,
      fill N i₁ (p.1 : ℝ) (p.2 : ℝ) ∈ punctured N :=
    fun _ => fill_ne_zero N i₁ h₁ _ _
  have hsq : Continuous fun p : unitInterval × unitInterval =>
      g (fill N i₁ (p.1 : ℝ) (p.2 : ℝ)) := hcont.comp_continuous hcf hmem
  refine no_winding_square (g (basePoint N)) hcne
    (fun p => g (fill N i₁ (p.1 : ℝ) (p.2 : ℝ))) hsq ?_ ?_ ?_ ?_ ?_
  · exact fun p => hne _ (hmem p)
  · intro t
    show g (fill N i₁ (0 : ℝ) (t : ℝ))
        = (circleLoop (t : ℝ))⁻¹ * g (basePoint N)
    rw [fill_zero_left]
    exact hhom (circleLoop (t : ℝ)) (basePoint N) (circleLoop_ne_zero _) hbase
  · intro t
    show g (fill N i₁ (1 : ℝ) (t : ℝ)) = g (basePoint N)
    rw [fill_one_left]
  · intro s
    show g (fill N i₁ (s : ℝ) (0 : ℝ)) = g (basePoint N)
    rw [fill_zero_right]
  · intro s
    show g (fill N i₁ (s : ℝ) (1 : ℝ)) = g (basePoint N)
    rw [fill_one_right]

/-- The rank-one case of `TautologicalCommonZero.CommonZeroProperty`: over
`ℂPᴺ` with `N ≥ 1`, a section of `L^{⊕κ}` with `κ` a subsingleton has a
zero. -/
theorem exists_zero_of_subsingleton {N : ℕ} (hN : 1 ≤ N) {κ : Type*} [Subsingleton κ]
    (f : TautSection N κ) : ∃ z : Fin (N + 1) → ℂ, z ≠ 0 ∧ f.toFun z = 0 := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · refine ⟨basePoint N, basePoint_ne_zero N, ?_⟩
    funext k
    exact (hκ.false k).elim
  · obtain ⟨k₀⟩ := hκ
    by_contra hcon
    refine not_nonvanishing_homogeneous hN (f.component k₀)
      (f.continuousOn_component k₀) (fun c z hc hz => f.component_smul k₀ c z hc hz) ?_
    intro z hz hzero
    refine hcon ⟨z, hz, ?_⟩
    funext k
    have hk : k = k₀ := Subsingleton.elim k k₀
    rw [hk]
    exact hzero

/-- The same conclusion phrased with `Nat.card`, matching the shape of
`TautologicalCommonZero.CommonZeroProperty`. -/
theorem exists_zero_of_card_le_one {N : ℕ} (hN : 1 ≤ N) {κ : Type} [Finite κ]
    (hκ : Nat.card κ ≤ 1) (f : TautSection N κ) :
    ∃ z : Fin (N + 1) → ℂ, z ≠ 0 ∧ f.toFun z = 0 := by
  haveI : Subsingleton κ := Finite.card_le_one_iff_subsingleton.mp hκ
  exact exists_zero_of_subsingleton hN f

/-- The family form of the rank-one theorem. -/
theorem hasCommonZero_of_subsingleton {N : ℕ} (hN : 1 ≤ N) {ι κ : Type*}
    [Subsingleton ι] [Subsingleton κ] (F : ι → TautSection N κ) :
    HasCommonZero F := by
  haveI : Subsingleton (ι × κ) :=
    ⟨fun a b => by
      obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      rw [Subsingleton.elim a1 b1, Subsingleton.elim a2 b2]⟩
  rw [hasCommonZero_iff_join]
  exact exists_zero_of_subsingleton hN (join F)

/-- **The `s = ℓ = 1` block of the STW Problem XXII counterexample.**  Over
`ℂP^(1²) = ℂP¹`, one continuous section of `L^{⊕1}` has a zero -- and this is
proved, not assumed. -/
theorem hasCommonZero_one_one (F : Fin 1 → TautSection (1 * 1) (Fin 1)) :
    HasCommonZero F := by
  have hN : (1 : ℕ) ≤ 1 * 1 := by norm_num
  exact hasCommonZero_of_subsingleton hN F

end

end TautologicalLineWinding
end GroupApproximation
