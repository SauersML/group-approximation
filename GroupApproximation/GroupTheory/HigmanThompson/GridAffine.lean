import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import GroupApproximation.Meta.AxiomGuard

/-!
# Grid-affine bijections of `ℚ`

The finitely presented simple group of `non_mf_groups_exist.tex`, Section 5, is a
Hyde–Lodha group (Fournier-Facio's §2 names "a Burger–Mozes or Hyde–Lodha group").
Hyde and Lodha build it from piecewise linear homeomorphisms of the line whose
breakpoints lie in `ℤ[1/m]` and whose slopes lie in a multiplicative group `Ω`.
This module sets up the piecewise linear layer.

A map is recorded here through the rationals, where every map of the relevant
class sends `ℚ` to `ℚ` and all arithmetic is exact, and "finitely many breakpoints
in each bounded interval, all in `ℤ[1/m]`" is recorded as **uniform grid
affinity**: there is a level `N` such that `f` is affine on every interval
`[k/m^N, (k+1)/m^N]`, and a bound `B` such that every slope and every value at a
level-`N` grid point lies in `m^{-B} ℤ`.

The one real lemma is `GridAffine.comp`: composing with a grid-affine strictly
increasing bijection whose inverse is grid-affine gives a grid-affine map, at an
explicit finer level.  `PLGroup m Ω` is the resulting subgroup of `Equiv.Perm ℚ`.
-/

namespace GroupApproximation
namespace HigmanThompson

/-! ## Definitions -/

section Defs

variable (m : ℕ)

/-- The points of `ℤ[1/m]` of level `N`: the rationals `x` with `x · m^N ∈ ℤ`. -/
def Grid (N : ℕ) : Set ℚ := {x | ∃ k : ℤ, x * (m : ℚ) ^ N = k}

/-- The `k`-th grid point of level `N`, `k / m^N`. -/
def gridPt (N : ℕ) (k : ℤ) : ℚ := (k : ℚ) / (m : ℚ) ^ N

/-- `f` is affine with slope `s` on the closed interval `[a, b]`. -/
def AffineOn (f : ℚ → ℚ) (a b s : ℚ) : Prop :=
  ∀ x, a ≤ x → x ≤ b → f x = f a + s * (x - a)

/-- **Uniform grid affinity.**  `f` is affine on every level-`N` grid interval with a
slope in `Ω`; every such slope and every value of `f` at a level-`N` grid point lies
in `Grid m B`. -/
structure GridAffine (Ω : Submonoid ℚ) (f : ℚ → ℚ) (N B : ℕ) : Prop where
  slope : ∀ k : ℤ, ∃ s ∈ Ω, s ∈ Grid m B ∧ AffineOn f (gridPt m N k) (gridPt m N (k + 1)) s
  value : ∀ k : ℤ, f (gridPt m N k) ∈ Grid m B

end Defs

/-! ## The grid -/

section GridArith

variable {m : ℕ}

theorem grid_mono {N N' : ℕ} (h : N ≤ N') : Grid m N ⊆ Grid m N' := by
  rintro x ⟨k, hk⟩
  refine ⟨k * (m : ℤ) ^ (N' - N), ?_⟩
  have hpow : (m : ℚ) ^ N' = (m : ℚ) ^ N * (m : ℚ) ^ (N' - N) := by
    rw [← pow_add, Nat.add_sub_of_le h]
  rw [hpow, ← mul_assoc, hk]
  push_cast
  ring

theorem grid_add {N : ℕ} {x y : ℚ} (hx : x ∈ Grid m N) (hy : y ∈ Grid m N) :
    x + y ∈ Grid m N := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨l, hl⟩ := hy
  exact ⟨k + l, by rw [add_mul, hk, hl]; push_cast; ring⟩

theorem grid_neg {N : ℕ} {x : ℚ} (hx : x ∈ Grid m N) : -x ∈ Grid m N := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨-k, by rw [neg_mul, hk]; push_cast; ring⟩

theorem grid_sub {N : ℕ} {x y : ℚ} (hx : x ∈ Grid m N) (hy : y ∈ Grid m N) :
    x - y ∈ Grid m N := by
  rw [sub_eq_add_neg]
  exact grid_add hx (grid_neg hy)

theorem grid_mul {a b : ℕ} {x y : ℚ} (hx : x ∈ Grid m a) (hy : y ∈ Grid m b) :
    x * y ∈ Grid m (a + b) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨l, hl⟩ := hy
  refine ⟨k * l, ?_⟩
  calc x * y * (m : ℚ) ^ (a + b) = (x * (m : ℚ) ^ a) * (y * (m : ℚ) ^ b) := by
        rw [pow_add]; ring
    _ = ((k * l : ℤ) : ℚ) := by rw [hk, hl]; push_cast; ring

theorem int_mem_grid (N : ℕ) (k : ℤ) : (k : ℚ) ∈ Grid m N :=
  grid_mono (Nat.zero_le N) ⟨k, by simp⟩

end GridArith

section GridOrder

variable {m : ℕ} [hm : Fact (1 < m)]

theorem mPow_pos (N : ℕ) : (0 : ℚ) < (m : ℚ) ^ N := by
  have h : (0 : ℚ) < m := by exact_mod_cast lt_trans Nat.zero_lt_one hm.out
  exact pow_pos h N

theorem gridPt_mem (N : ℕ) (k : ℤ) : gridPt m N k ∈ Grid m N :=
  ⟨k, by unfold gridPt; exact div_mul_cancel₀ _ (mPow_pos N).ne'⟩

theorem gridPt_le_iff {N : ℕ} {k : ℤ} {x : ℚ} :
    gridPt m N k ≤ x ↔ (k : ℚ) ≤ x * (m : ℚ) ^ N := by
  unfold gridPt
  exact div_le_iff₀ (mPow_pos N)

theorem lt_gridPt_iff {N : ℕ} {k : ℤ} {x : ℚ} :
    x < gridPt m N k ↔ x * (m : ℚ) ^ N < k := by
  unfold gridPt
  exact lt_div_iff₀ (mPow_pos N)

theorem gridPt_lt_iff {N : ℕ} {k : ℤ} {x : ℚ} :
    gridPt m N k < x ↔ (k : ℚ) < x * (m : ℚ) ^ N := by
  unfold gridPt
  exact div_lt_iff₀ (mPow_pos N)

/-- The level-`N` grid interval of `x`: `⌊x m^N⌋ / m^N ≤ x < (⌊x m^N⌋ + 1) / m^N`. -/
theorem floor_bracket (N : ℕ) (x : ℚ) :
    gridPt m N ⌊x * (m : ℚ) ^ N⌋ ≤ x ∧ x < gridPt m N (⌊x * (m : ℚ) ^ N⌋ + 1) := by
  constructor
  · rw [gridPt_le_iff]
    exact Int.floor_le _
  · rw [lt_gridPt_iff]
    push_cast
    exact Int.lt_floor_add_one _

/-- No level-`L` grid point lies strictly between two consecutive level-`L` grid points. -/
theorem not_between_consecutive {L : ℕ} {k : ℤ} {q : ℚ} (hq : q ∈ Grid m L) :
    ¬ (gridPt m L k < q ∧ q < gridPt m L (k + 1)) := by
  rintro ⟨h1, h2⟩
  obtain ⟨j, hj⟩ := hq
  rw [gridPt_lt_iff, hj] at h1
  rw [lt_gridPt_iff, hj] at h2
  have h1' : k < j := by exact_mod_cast h1
  have h2' : j < k + 1 := by exact_mod_cast h2
  omega

/-- An interval `[u, v]` with no level-`M` grid point strictly inside lies in one
level-`M` grid interval. -/
theorem exists_bracket_of_no_grid {M : ℕ} {u v : ℚ}
    (hno : ∀ q ∈ Grid m M, ¬ (u < q ∧ q < v)) :
    ∃ k : ℤ, gridPt m M k ≤ u ∧ v ≤ gridPt m M (k + 1) := by
  refine ⟨⌊u * (m : ℚ) ^ M⌋, (floor_bracket M u).1, ?_⟩
  by_contra hlt
  exact hno _ (gridPt_mem M _) ⟨(floor_bracket M u).2, not_le.mp hlt⟩

end GridOrder

/-! ## Affine pieces -/

theorem AffineOn.restrict {f : ℚ → ℚ} {a b a' b' s : ℚ} (h : AffineOn f a b s)
    (ha : a ≤ a') (hb : b' ≤ b) : AffineOn f a' b' s := by
  intro x hx1 hx2
  have hxa : f x = f a + s * (x - a) := h x (le_trans ha hx1) (le_trans hx2 hb)
  have ha' : f a' = f a + s * (a' - a) := h a' ha (le_trans hx1 (le_trans hx2 hb))
  rw [hxa, ha']
  ring

section GridAffineLemmas

variable {m : ℕ} [hm : Fact (1 < m)] {Ω : Submonoid ℚ}

/-- A uniformly grid-affine map sends `ℤ[1/m]` into `ℤ[1/m]`, with an explicit level. -/
theorem GridAffine.mapsGrid {f : ℚ → ℚ} {N B : ℕ} (hf : GridAffine m Ω f N B)
    {M : ℕ} {q : ℚ} (hq : q ∈ Grid m M) : f q ∈ Grid m (B + max M N) := by
  obtain ⟨s, -, hsB, haff⟩ := hf.slope ⌊q * (m : ℚ) ^ N⌋
  have hbr := floor_bracket (m := m) N q
  rw [haff q hbr.1 hbr.2.le]
  refine grid_add (grid_mono (Nat.le_add_right B _) (hf.value _)) ?_
  exact grid_mul hsB (grid_sub (grid_mono (le_max_left M N) hq)
    (grid_mono (le_max_right M N) (gridPt_mem N _)))

/-- Affinity at every finer level. -/
theorem GridAffine.affine_fine {f : ℚ → ℚ} {N B : ℕ} (hf : GridAffine m Ω f N B)
    {L : ℕ} (hL : N ≤ L) (k : ℤ) :
    ∃ s ∈ Ω, s ∈ Grid m B ∧ AffineOn f (gridPt m L k) (gridPt m L (k + 1)) s := by
  obtain ⟨j, hj1, hj2⟩ := exists_bracket_of_no_grid (m := m) (M := N)
    (u := gridPt m L k) (v := gridPt m L (k + 1))
    (fun q hq => not_between_consecutive (grid_mono hL hq))
  obtain ⟨s, hsΩ, hsB, haff⟩ := hf.slope j
  exact ⟨s, hsΩ, hsB, haff.restrict hj1 hj2⟩

/-- **Composition.**  If `f` is a strictly increasing grid-affine map with a
grid-affine right inverse `finv`, and `g` is grid-affine, then `g ∘ f` is grid-affine
at the level `max Nf (Bi + max Ng Ni)`.  On a grid interval of that level `f` is
affine, and its image contains no level-`Ng` grid point in its interior, because the
preimage of such a point is a grid point of the finer level. -/
theorem GridAffine.comp {f finv g : ℚ → ℚ} {Nf Bf Ni Bi Ng Bg : ℕ}
    (hf : GridAffine m Ω f Nf Bf) (hfi : GridAffine m Ω finv Ni Bi)
    (hg : GridAffine m Ω g Ng Bg) (hmono : StrictMono f)
    (hright : ∀ y, f (finv y) = y) :
    GridAffine m Ω (g ∘ f) (max Nf (Bi + max Ng Ni))
      (Bg + max (Bf + max Nf (Bi + max Ng Ni)) Ng) := by
  refine ⟨fun k => ?_, fun k => ?_⟩
  · obtain ⟨sf, hsfΩ, hsfB, hfaff⟩ := hf.affine_fine (le_max_left Nf (Bi + max Ng Ni)) k
    have hno : ∀ q ∈ Grid m Ng,
        ¬ (f (gridPt m (max Nf (Bi + max Ng Ni)) k) < q ∧
          q < f (gridPt m (max Nf (Bi + max Ng Ni)) (k + 1))) := by
      rintro q hq ⟨h1, h2⟩
      have hqi : finv q ∈ Grid m (max Nf (Bi + max Ng Ni)) :=
        grid_mono (le_max_right Nf (Bi + max Ng Ni)) (hfi.mapsGrid hq)
      have h1' : gridPt m (max Nf (Bi + max Ng Ni)) k < finv q := by
        rw [← hmono.lt_iff_lt, hright]
        exact h1
      have h2' : finv q < gridPt m (max Nf (Bi + max Ng Ni)) (k + 1) := by
        rw [← hmono.lt_iff_lt, hright]
        exact h2
      exact not_between_consecutive hqi ⟨h1', h2'⟩
    obtain ⟨j, hj1, hj2⟩ := exists_bracket_of_no_grid hno
    obtain ⟨sg, hsgΩ, hsgB, hgaff⟩ := hg.slope j
    refine ⟨sg * sf, Ω.mul_mem hsgΩ hsfΩ,
      grid_mono (Nat.add_le_add_left
        (le_trans (Nat.le_add_right Bf _) (le_max_left _ Ng)) Bg) (grid_mul hsgB hsfB), ?_⟩
    intro x hx1 hx2
    have hfx : f x = f (gridPt m (max Nf (Bi + max Ng Ni)) k) +
        sf * (x - gridPt m (max Nf (Bi + max Ng Ni)) k) := hfaff x hx1 hx2
    have hgx := (hgaff.restrict hj1 hj2) (f x) (hmono.monotone hx1) (hmono.monotone hx2)
    show g (f x) = g (f (gridPt m (max Nf (Bi + max Ng Ni)) k)) +
      sg * sf * (x - gridPt m (max Nf (Bi + max Ng Ni)) k)
    rw [hgx, hfx]
    ring
  · have h1 := hf.mapsGrid (gridPt_mem (m := m) (max Nf (Bi + max Ng Ni)) k)
    have h2 := hg.mapsGrid h1
    rw [max_eq_left (le_max_left Nf (Bi + max Ng Ni))] at h2
    exact h2

/-- Raising the bound. -/
theorem GridAffine.mono_bound {f : ℚ → ℚ} {N B B' : ℕ} (hf : GridAffine m Ω f N B)
    (hB : B ≤ B') : GridAffine m Ω f N B' := by
  refine ⟨fun k => ?_, fun k => grid_mono hB (hf.value k)⟩
  obtain ⟨s, hsΩ, hsB, haff⟩ := hf.slope k
  exact ⟨s, hsΩ, grid_mono hB hsB, haff⟩

/-- Raising the level. -/
theorem GridAffine.mono_level {f : ℚ → ℚ} {N B N' : ℕ} (hf : GridAffine m Ω f N B)
    (hN : N ≤ N') : GridAffine m Ω f N' (B + N') := by
  refine ⟨fun k => ?_, fun k => ?_⟩
  · obtain ⟨s, hsΩ, hsB, haff⟩ := hf.affine_fine hN k
    exact ⟨s, hsΩ, grid_mono (Nat.le_add_right B N') hsB, haff⟩
  · have h := hf.mapsGrid (gridPt_mem (m := m) N' k)
    rwa [max_eq_left hN] at h

/-- **Gluing.**  A function agreeing with a grid-affine function on `(-∞, p]` and with
another on `[p, ∞)`, for a level-`N` grid point `p`, is grid-affine. -/
theorem GridAffine.glue {f g₁ g₂ : ℚ → ℚ} {N B : ℕ} (h₁ : GridAffine m Ω g₁ N B)
    (h₂ : GridAffine m Ω g₂ N B) {p : ℚ} (hp : p ∈ Grid m N)
    (hf₁ : ∀ t, t ≤ p → f t = g₁ t) (hf₂ : ∀ t, p ≤ t → f t = g₂ t) :
    GridAffine m Ω f N B := by
  have hside : ∀ k : ℤ, gridPt m N (k + 1) ≤ p ∨ p ≤ gridPt m N k := by
    intro k
    by_contra h
    push_neg at h
    exact not_between_consecutive hp ⟨h.2, h.1⟩
  refine ⟨fun k => ?_, fun k => ?_⟩
  · have hab : gridPt m N k ≤ gridPt m N (k + 1) := by
      rw [gridPt_le_iff]
      have h := (floor_bracket (m := m) N (gridPt m N (k + 1))).1
      have e : gridPt m N (k + 1) * (m : ℚ) ^ N = ((k + 1 : ℤ) : ℚ) := by
        unfold gridPt
        exact div_mul_cancel₀ _ (mPow_pos N).ne'
      rw [e]
      push_cast
      linarith
    rcases hside k with h | h
    · obtain ⟨s, hsΩ, hsB, haff⟩ := h₁.slope k
      refine ⟨s, hsΩ, hsB, fun x hx1 hx2 => ?_⟩
      rw [hf₁ x (le_trans hx2 h), hf₁ _ (le_trans hab h)]
      exact haff x hx1 hx2
    · obtain ⟨s, hsΩ, hsB, haff⟩ := h₂.slope k
      refine ⟨s, hsΩ, hsB, fun x hx1 hx2 => ?_⟩
      rw [hf₂ x (le_trans h hx1), hf₂ _ h]
      exact haff x hx1 hx2
  · rcases hside k with h | h
    · have hk : gridPt m N k ≤ p := by
        refine le_trans ?_ h
        rw [gridPt_le_iff]
        have e : gridPt m N (k + 1) * (m : ℚ) ^ N = ((k + 1 : ℤ) : ℚ) := by
          unfold gridPt
          exact div_mul_cancel₀ _ (mPow_pos N).ne'
        rw [e]
        push_cast
        linarith
      rw [hf₁ _ hk]
      exact h₁.value k
    · rw [hf₂ _ h]
      exact h₂.value k

/-- **Inverses.**  A strictly increasing grid-affine map with a two-sided inverse, whose
slopes have inverses in `Ω ∩ Grid m B'`, has a grid-affine inverse (at the level `B` of its
values).  On a level-`B` grid interval no value `f (k / m^N)` lies strictly inside, so the
interval sits inside the image of one affine piece. -/
theorem GridAffine.inverse {f finv : ℚ → ℚ} {N B B' : ℕ} (hf : GridAffine m Ω f N B)
    (hmono : StrictMono f) (hleft : ∀ x, finv (f x) = x) (hright : ∀ y, f (finv y) = y)
    (hinv : ∀ k : ℤ, ∀ s : ℚ, AffineOn f (gridPt m N k) (gridPt m N (k + 1)) s →
      s⁻¹ ∈ Ω ∧ s⁻¹ ∈ Grid m B') :
    GridAffine m Ω finv B (N + B' + B) := by
  have hstep : ∀ k : ℤ, gridPt m N k < gridPt m N (k + 1) := by
    intro k
    rw [gridPt_lt_iff]
    have e : gridPt m N (k + 1) * (m : ℚ) ^ N = ((k + 1 : ℤ) : ℚ) := by
      unfold gridPt
      exact div_mul_cancel₀ _ (mPow_pos N).ne'
    rw [e]
    push_cast
    linarith
  -- the piece of `f` whose image contains a given level-`B` grid interval
  have hpiece : ∀ k' : ℤ, ∃ k : ℤ, f (gridPt m N k) ≤ gridPt m B k' ∧
      gridPt m B (k' + 1) ≤ f (gridPt m N (k + 1)) := by
    intro k'
    set c := gridPt m B k'
    obtain ⟨h1, h2⟩ := floor_bracket (m := m) N (finv c)
    refine ⟨⌊finv c * (m : ℚ) ^ N⌋, ?_, ?_⟩
    · have h := hmono.monotone h1
      rwa [hright] at h
    · by_contra hlt
      have hlt' := not_le.mp hlt
      have hc : c < f (gridPt m N (⌊finv c * (m : ℚ) ^ N⌋ + 1)) := by
        have h := hmono h2
        rwa [hright] at h
      exact not_between_consecutive (hf.value _) ⟨hc, hlt'⟩
  refine ⟨fun k' => ?_, fun k' => ?_⟩
  · obtain ⟨k, hk1, hk2⟩ := hpiece k'
    obtain ⟨s, -, -, haff⟩ := hf.slope k
    obtain ⟨hsΩ, hsB'⟩ := hinv k s haff
    have hs : 0 < s := by
      have h1 := haff (gridPt m N (k + 1)) (hstep k).le le_rfl
      have h2 := hmono (hstep k)
      have h3 : 0 < gridPt m N (k + 1) - gridPt m N k := sub_pos.mpr (hstep k)
      nlinarith
    have hform : ∀ y, f (gridPt m N k) ≤ y → y ≤ f (gridPt m N (k + 1)) →
        finv y = gridPt m N k + s⁻¹ * (y - f (gridPt m N k)) := by
      intro y hy1 hy2
      have hx1 : gridPt m N k ≤ finv y := by
        by_contra h
        have h' := hmono (not_le.mp h)
        rw [hright] at h'
        linarith
      have hx2 : finv y ≤ gridPt m N (k + 1) := by
        by_contra h
        have h' := hmono (not_le.mp h)
        rw [hright] at h'
        linarith
      have hy := haff (finv y) hx1 hx2
      rw [hright] at hy
      have hs0 : s ≠ 0 := hs.ne'
      field_simp
      linarith
    refine ⟨s⁻¹, hsΩ, grid_mono (by omega) hsB', fun y hy1 hy2 => ?_⟩
    have hcy : f (gridPt m N k) ≤ gridPt m B k' := hk1
    have hyd : y ≤ f (gridPt m N (k + 1)) := le_trans hy2 hk2
    rw [hform y (le_trans hcy hy1) hyd, hform _ hcy (le_trans (le_trans hy1 hy2) hk2)]
    ring
  · obtain ⟨k, hk1, hk2⟩ := hpiece k'
    obtain ⟨s, -, -, haff⟩ := hf.slope k
    obtain ⟨-, hsB'⟩ := hinv k s haff
    have hs : 0 < s := by
      have h1 := haff (gridPt m N (k + 1)) (hstep k).le le_rfl
      have h2 := hmono (hstep k)
      have h3 : 0 < gridPt m N (k + 1) - gridPt m N k := sub_pos.mpr (hstep k)
      nlinarith
    have hx1 : gridPt m N k ≤ finv (gridPt m B k') := by
      by_contra h
      have h' := hmono (not_le.mp h)
      rw [hright] at h'
      linarith
    have hstepB : gridPt m B k' ≤ gridPt m B (k' + 1) := by
      rw [gridPt_le_iff]
      have e : gridPt m B (k' + 1) * (m : ℚ) ^ B = ((k' + 1 : ℤ) : ℚ) := by
        unfold gridPt
        exact div_mul_cancel₀ _ (mPow_pos B).ne'
      rw [e]
      push_cast
      linarith
    have hx2 : finv (gridPt m B k') ≤ gridPt m N (k + 1) := by
      by_contra h
      have h' := hmono (not_le.mp h)
      rw [hright] at h'
      linarith
    have hy := haff _ hx1 hx2
    rw [hright] at hy
    have hval : finv (gridPt m B k') =
        gridPt m N k + s⁻¹ * (gridPt m B k' - f (gridPt m N k)) := by
      have hs0 : s ≠ 0 := hs.ne'
      field_simp
      linarith
    rw [hval]
    refine grid_add (grid_mono (by omega) (gridPt_mem N k)) ?_
    have hprod := grid_mul hsB' (grid_sub (gridPt_mem (m := m) B k') (hf.value k))
    exact grid_mono (by omega) hprod

/-- An affine map `t ↦ s t + b` with `s ∈ Ω` and `s, b ∈ Grid m B` is grid-affine. -/
theorem gridAffine_affine {s b : ℚ} {B : ℕ} (hsΩ : s ∈ Ω) (hsB : s ∈ Grid m B)
    (hb : b ∈ Grid m B) : GridAffine m Ω (fun t => s * t + b) 0 B := by
  refine ⟨fun k => ⟨s, hsΩ, hsB, fun x _ _ => by ring⟩, fun k => ?_⟩
  have e : gridPt m 0 k = (k : ℚ) := by simp [gridPt]
  show s * gridPt m 0 k + b ∈ Grid m B
  rw [e]
  have h := grid_mul hsB (int_mem_grid (m := m) 0 k)
  rw [add_zero] at h
  exact grid_add h hb

theorem gridAffine_id : GridAffine m Ω id 0 0 := by
  refine ⟨fun k => ⟨1, Ω.one_mem, ?_, fun x _ _ => ?_⟩, fun k => ?_⟩
  · simpa using int_mem_grid (m := m) 0 1
  · simp only [id, one_mul]
    ring
  · exact gridPt_mem 0 k

end GridAffineLemmas

/-! ## The group -/

theorem strictMono_perm_inv {f : Equiv.Perm ℚ} (hf : StrictMono f) : StrictMono ⇑f⁻¹ := by
  intro x y hxy
  by_contra h
  have h' := hf.monotone (not_lt.mp h)
  rw [Equiv.Perm.apply_inv_self, Equiv.Perm.apply_inv_self] at h'
  exact absurd hxy (not_lt.mpr h')

section Group

variable (m : ℕ) [hm : Fact (1 < m)] (Ω : Submonoid ℚ)

/-- **The piecewise linear group of `ℚ` over `(ℤ[1/m], Ω)`**: strictly increasing
bijections `f` of `ℚ` such that `f` and `f⁻¹` are both uniformly grid-affine with
slopes in `Ω`. -/
def PLGroup : Subgroup (Equiv.Perm ℚ) where
  carrier := {f | StrictMono f ∧ (∃ N B, GridAffine m Ω f N B) ∧
    (∃ N B, GridAffine m Ω ⇑f⁻¹ N B)}
  one_mem' := ⟨strictMono_id, ⟨0, 0, gridAffine_id⟩, ⟨0, 0, gridAffine_id⟩⟩
  mul_mem' := by
    rintro f g ⟨hfm, ⟨Nf, Bf, hf⟩, ⟨Nfi, Bfi, hfi⟩⟩ ⟨hgm, ⟨Ng, Bg, hg⟩, ⟨Ngi, Bgi, hgi⟩⟩
    refine ⟨?_, ⟨_, _, ?_⟩, ⟨_, _, ?_⟩⟩
    · show StrictMono (⇑f ∘ ⇑g)
      exact hfm.comp hgm
    · show GridAffine m Ω (⇑f ∘ ⇑g) _ _
      exact hg.comp hgi hf hgm (fun y => Equiv.Perm.apply_inv_self g y)
    · have hinv : ⇑(f * g)⁻¹ = ⇑g⁻¹ ∘ ⇑f⁻¹ := by
        ext x
        simp [mul_inv_rev, Equiv.Perm.mul_apply]
      rw [hinv]
      exact hfi.comp hf hgi (strictMono_perm_inv hfm) (fun y => Equiv.Perm.inv_apply_self f y)
  inv_mem' := by
    rintro f ⟨hfm, hf, hfi⟩
    refine ⟨strictMono_perm_inv hfm, hfi, ?_⟩
    simpa only [inv_inv] using hf

theorem mem_PLGroup {f : Equiv.Perm ℚ} :
    f ∈ PLGroup m Ω ↔ StrictMono f ∧ (∃ N B, GridAffine m Ω f N B) ∧
      (∃ N B, GridAffine m Ω ⇑f⁻¹ N B) := Iff.rfl

end Group

#audit_axioms GroupApproximation.HigmanThompson.GridAffine.comp
#audit_axioms GroupApproximation.HigmanThompson.GridAffine.mapsGrid
#audit_axioms GroupApproximation.HigmanThompson.mem_PLGroup

end HigmanThompson
end GroupApproximation
