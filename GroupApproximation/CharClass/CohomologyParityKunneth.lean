import GroupApproximation.CharClass.CohomologyKunnethParity
import GroupApproximation.CharClass.SqDataInstance

/-!
# Künneth for the two sphere factors of the mapping-torus base

`cc-wu`'s `htx_inj` field asks that the `t x`-coordinate of a class of
`H^*(S¹ × S⁵ × Y)` be well defined: if `ι u + t x ι v = 0` then `v = 0`.  That is
Künneth injectivity for **two** sphere factors, and it comes from the one-factor
statement applied twice, peeling one sphere at a time.

The base is written left-nested as `(Y × S⁵) × S¹`, because `KnHemi`'s Künneth
lemma always puts the new sphere on the right.  The circle is peeled first: a
slice of the circle factor kills `t`, which forces the `ι u` summand to vanish,
and what is left is one application of the one-factor lemma over the base
`Y × S⁵`, then a second over `Y`.

The ring-level statement is the degreewise one read off componentwise.  The
component of a product `of i w * z` at `i + m` is `w ⌣ (component m z)`, which is
`component_of_mul` below; with `cc-wu`'s `totalH_component_map` for the pullback,
the field reduces to `KnTwo.tx_inj_degree` at each degree.

## Main declarations

* `KnTwo.torusBase`, `KnTwo.prY`, `KnTwo.prS1`, `KnTwo.prS5` — the model and its
  three projections.
* `KnTwo.tx_inj_degree` — the degreewise statement.
* `KnTwo.htx_inj` — `cc-wu`'s field.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnTwo

/-! ## 0. The component of a product -/

/-- **The component of `of i w * z` at `i + m` is `w ⌣ (component m z)`.**  In the
lane sub-namespace: `cc-wu` has a differently-shaped `component_of_mul` in
`GroupApproximation.CharClass.Wu`, and two short names at different depths are an
ambiguity waiting to happen. -/
theorem component_of_mul {X : TopCat.{0}} (i m : ℕ) (w : TotalPiece X i) (z : TotalH X) :
    TotalH.component X (i + m) (TotalH.of X i w * z) = cup w (TotalH.component X m z) := by
  induction z using DirectSum.induction_on with
  | zero => rw [mul_zero, map_zero, map_zero, cup_zero]
  | of j c =>
    show TotalH.component X (i + m) (TotalH.of X i w * TotalH.of X j c)
      = cup w (TotalH.component X m (TotalH.of X j c))
    rw [← TotalH.of_mul]
    rcases eq_or_ne j m with rfl | hjm
    · rw [TotalH.component_of, TotalH.component_of]
    · rw [Wu.component_of_ne (show i + m ≠ i + j by omega), Wu.component_of_ne hjm.symm,
        cup_zero]
  | add z₁ z₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, cup_add_right]

variable (Y : Type) [TopologicalSpace Y]

/-! ## 1. The model and its projections -/

/-- The intermediate base `Y × S⁵`. -/
abbrev midBase : Type := Y × Sphere 5

/-- The mapping-torus base, left-nested as `(Y × S⁵) × S¹`. -/
abbrev torusBase : Type := midBase Y × Sphere 1

/-- The mapping-torus base as an object of `TopCat`. -/
abbrev NTop : TopCat.{0} := TopCat.of (torusBase Y)

/-- The fibre base as an object of `TopCat`. -/
abbrev YTop : TopCat.{0} := TopCat.of Y

/-- The projection to `Y`. -/
def prY : NTop Y ⟶ YTop Y := knPrY (midBase Y) 1 ≫ knPrY Y 5

/-- The projection to the circle factor. -/
def prS1 : NTop Y ⟶ TopCat.of (Sphere 1) := knPrS (midBase Y) 1

/-- The projection to the `S⁵` factor. -/
def prS5 : NTop Y ⟶ TopCat.of (Sphere 5) := knPrY (midBase Y) 1 ≫ knPrS Y 5

/-- The degree-one generator on the base. -/
def sig1 : Hmod2 (NTop Y) 1 := knSigma (midBase Y) 1 (by omega)

/-- The degree-five generator on the base. -/
def sig5 : Hmod2 (NTop Y) 5 := pull (knPrY (midBase Y) 1) 5 (knSigma Y 5 (by omega))

theorem pull_prS1 : pull (prS1 Y) 1 (sphereTopClass 1 (by omega)) = sig1 Y := rfl

theorem pull_prS5 : pull (prS5 Y) 5 (sphereTopClass 5 (by omega)) = sig5 Y := by
  rw [prS5, pull_comp]
  rfl

/-! ## 2. The degreewise statement -/

set_option maxHeartbeats 1000000 in
/-- **Künneth injectivity for the two sphere factors, in a single degree.** -/
theorem tx_inj_degree (m : ℕ) (uu : Hmod2 (YTop Y) (1 + 5 + m))
    (vv : Hmod2 (YTop Y) m)
    (h : pull (prY Y) (1 + 5 + m) uu
      + cup (cup (sig1 Y) (sig5 Y)) (pull (prY Y) m vv) = 0) : vv = 0 := by
  have hslice : ∀ (k : ℕ) (a : Hmod2 (YTop Y) k),
      pull (knSlice (midBase Y) 1 (northPole 0)) k (pull (prY Y) k a)
        = pull (knPrY Y 5) k a := by
    intro k a
    rw [prY, pull_comp, pull_knSlice_knPrY]
  have hsig1 : pull (knSlice (midBase Y) 1 (northPole 0)) 1 (sig1 Y) = 0 :=
    pull_knSlice_knSigma (midBase Y) 1 (by omega) (northPole 0)
  -- the circle slice kills the `t x` term, so the first summand vanishes
  have hU : pull (knPrY Y 5) (1 + 5 + m) uu = 0 := by
    have hh := congrArg (pull (knSlice (midBase Y) 1 (northPole 0)) (1 + 5 + m)) h
    rw [pull_add, pull_zero, hslice, pull_cup, pull_cup, hsig1, zero_cup, zero_cup,
      add_zero] at hh
    exact hh
  have h2 : cup (cup (sig1 Y) (sig5 Y)) (pull (prY Y) m vv) = 0 := by
    have hz : pull (prY Y) (1 + 5 + m) uu = 0 := by
      rw [prY, pull_comp, hU, pull_zero]
    rwa [hz, zero_add] at h
  -- reassociate and peel the circle factor
  have h3 : cup (sig1 Y) (cup (sig5 Y) (pull (prY Y) m vv)) = 0 := by
    rw [← cup_assoc, h2]
    exact KnHemi.cohCast_zero _
  have h4 : cup (sig5 Y) (pull (prY Y) m vv)
      = pull (knPrY (midBase Y) 1) (5 + m)
          (cup (knSigma Y 5 (by omega)) (pull (knPrY Y 5) m vv)) := by
    rw [pull_cup, sig5, prY, pull_comp]
  have h5 : cup (knSigma Y 5 (by omega)) (pull (knPrY Y 5) m vv) = 0 := by
    refine KnHemi.kunnethSecondInjective (midBase Y) 1 (by omega) (5 + m) _ ?_
    rw [← h4]
    exact h3
  exact KnHemi.kunnethSecondInjective Y 5 (by omega) m vv h5

/-! ## 3. `cc-wu`'s field -/

/-- The product of the two sphere generators, as an element of the total ring. -/
theorem tClass_mul_xClass :
    Wu.tClass (prS1 Y) (sphereTopClass 1 (by omega))
        * Wu.xClass (prS5 Y) (sphereTopClass 5 (by omega))
      = TotalH.of (NTop Y) (1 + 5) (cup (sig1 Y) (sig5 Y)) := by
  rw [Wu.tClass, Wu.xClass, TotalH.map_of, TotalH.map_of, TotalH.of_mul, pull_prS1,
    pull_prS5]

set_option maxHeartbeats 1000000 in
/-- **`cc-wu`'s `htx_inj` field.**  The `t x`-coordinate of a class on the
mapping-torus base is well defined. -/
theorem htx_inj (u v : TotalH (YTop Y))
    (h : TotalH.map (prY Y) u
      + Wu.tClass (prS1 Y) (sphereTopClass 1 (by omega))
        * Wu.xClass (prS5 Y) (sphereTopClass 5 (by omega))
        * TotalH.map (prY Y) v = 0) : v = 0 := by
  refine DirectSum.ext _ (fun m => ?_)
  show TotalH.component (YTop Y) m v = TotalH.component (YTop Y) m (0 : TotalH (YTop Y))
  rw [map_zero]
  have hc := congrArg (TotalH.component (NTop Y) (1 + 5 + m)) h
  rw [map_add, map_zero, Wu.totalH_component_map, tClass_mul_xClass, component_of_mul,
    Wu.totalH_component_map] at hc
  exact tx_inj_degree Y m (TotalH.component (YTop Y) (1 + 5 + m) u)
    (TotalH.component (YTop Y) m v) hc

/-! ## 4. The four-term decomposition -/

theorem pull_prY_comp (k : ℕ) (c : Hmod2 (YTop Y) k) :
    pull (knPrY (midBase Y) 1) k (pull (knPrY Y 5) k c) = pull (prY Y) k c := by
  rw [prY, pull_comp]

set_option maxHeartbeats 1000000 in
/-- **The four-term Künneth decomposition of the mapping-torus base.**  A class of
degree `1 + 5 + m` on `(Y × S⁵) × S¹` is a pullback from `Y` plus a `t`-multiple,
plus an `x`-multiple, plus a `t x`-multiple.  The two middle terms are genuinely
there: `t ⌣ ι β` for `β` of degree two is a class of degree three, and the `t x`
part starts only in degree six. -/
theorem decomp_top (m : ℕ) (z : Hmod2 (NTop Y) (1 + 5 + m)) :
    ∃ (a : Hmod2 (YTop Y) (1 + 5 + m)) (a₁ : Hmod2 (YTop Y) (5 + m))
      (a₅ : Hmod2 (YTop Y) (1 + m)) (b : Hmod2 (YTop Y) m),
      z = pull (prY Y) (1 + 5 + m) a
        + cohCast (show 1 + (5 + m) = 1 + 5 + m by omega)
            (cup (sig1 Y) (pull (prY Y) (5 + m) a₁))
        + cohCast (show 5 + (1 + m) = 1 + 5 + m by omega)
            (cup (sig5 Y) (pull (prY Y) (1 + m) a₅))
        + cup (cup (sig1 Y) (sig5 Y)) (pull (prY Y) m b) := by
  obtain ⟨A, B, hAB⟩ := KnHemi.kunneth_decomposition (midBase Y) 1 (by omega)
    (1 + 5 + m) (5 + m) (by omega) z
  obtain ⟨a, a₅, hA⟩ := KnHemi.kunneth_decomposition Y 5 (by omega)
    (1 + 5 + m) (1 + m) (by omega) A
  obtain ⟨a₁, b, hB⟩ := KnHemi.kunneth_decomposition Y 5 (by omega)
    (5 + m) m (by omega) B
  refine ⟨a, a₁, a₅, b, ?_⟩
  have e1 : pull (knPrY (midBase Y) 1) (1 + 5 + m) A
      = pull (prY Y) (1 + 5 + m) a
        + cohCast (show 5 + (1 + m) = 1 + 5 + m by omega)
            (cup (sig5 Y) (pull (prY Y) (1 + m) a₅)) := by
    rw [hA, pull_add, pull_prY_comp, KnHemi.pull_cohCast, pull_cup, pull_prY_comp]
    rfl
  have e2 : pull (knPrY (midBase Y) 1) (5 + m) B
      = pull (prY Y) (5 + m) a₁ + cup (sig5 Y) (pull (prY Y) m b) := by
    rw [hB, cohCast_self, pull_add, pull_prY_comp, pull_cup, pull_prY_comp]
    rfl
  rw [hAB, e1, e2, cup_add_right, cohCast_add, cup_assoc']
  abel

/-! ## 5. `cc-wu`'s `hγ` and `hsq_b`

`decomp_top` shows that the general class on the base has four coordinates, so the
two-term form that `hγ` asserts is *not* a consequence of Künneth: it needs the
`t`- and `x`-coordinates of the Chern classes to vanish, which is a fact about
`γ` and belongs to `cc-projective`.  `ChernSplit` is exactly that input, with the
degrees the grading forces written in, and from it both `hγ` and `hsq_b` are
immediate. -/

theorem totalH_of_cohCast {X : TopCat.{0}} {n n' : ℕ} (h : n = n')
    (a : Hmod2 X n) : TotalH.of X n' (cohCast h a) = TotalH.of X n a := by
  subst h
  rw [cohCast_self]

/-- **What `cc-projective` supplies.**  Each mod-2 Chern class of `W` splits with no
`t`- and no `x`-coordinate, and its two coefficients sit in the degrees the grading
forces: `2k` for the pullback part and `2k - 6` for the `t x` part, the latter
vanishing while `2k < 6` because `t x` already carries degree six. -/
structure ChernSplit (γ : ℕ → TotalH (NTop Y)) where
  /-- The pullback coefficient, in degree `2k`. -/
  alpha : ∀ k : ℕ, Hmod2 (YTop Y) (2 * k)
  /-- The `t x` coefficient, in degree `2k - 6`. -/
  beta : ∀ k : ℕ, Hmod2 (YTop Y) (2 * k - 6)
  /-- There is no room for a `t x` part below total degree six. -/
  beta_low : ∀ k : ℕ, 2 * k < 6 → beta k = 0
  /-- The splitting itself. -/
  split : ∀ k : ℕ, γ k
      = TotalH.map (prY Y) (TotalH.of (YTop Y) (2 * k) (alpha k))
        + Wu.tClass (prS1 Y) (sphereTopClass 1 (by omega))
          * Wu.xClass (prS5 Y) (sphereTopClass 5 (by omega))
          * TotalH.map (prY Y) (TotalH.of (YTop Y) (2 * k - 6) (beta k))

/-- **`cc-wu`'s `hγ` and `hsq_b` fields, from the split.** -/
theorem hgamma_and_hsq_b (γ : ℕ → TotalH (NTop Y)) (S : ChernSplit Y γ) :
    ∃ a b : ℕ → TotalH (YTop Y),
      (∀ k : ℕ, γ k = TotalH.map (prY Y) (a k)
          + Wu.tClass (prS1 Y) (sphereTopClass 1 (by omega))
            * Wu.xClass (prS5 Y) (sphereTopClass 5 (by omega))
            * TotalH.map (prY Y) (b k))
        ∧ (∀ k j : ℕ, 2 * k < j + 6 → Steenrod.SqH (YTop Y) j (b k) = 0) := by
  refine ⟨fun k => TotalH.of (YTop Y) (2 * k) (S.alpha k),
    fun k => TotalH.of (YTop Y) (2 * k - 6) (S.beta k), S.split, ?_⟩
  refine Wu.sq_b_of_grading _ (fun k hk => ?_) (fun k c hc => ?_)
  · rw [S.beta_low k (by omega), map_zero]
  · exact ⟨cohCast (show 2 * k - 6 = c by omega) (S.beta k), (totalH_of_cohCast _ _).symm⟩

/-! ## 6. The even-degree two-term decomposition -/

set_option maxHeartbeats 1000000 in
/-- **The two-term decomposition in even degree.**  The two middle coordinates of the
four-term split sit in the odd degrees `m - 1` and `m - 5` of `Y`, so they vanish as
soon as `Y` has no odd cohomology.  No extra fact about the class is needed: its
even degree is what excludes them. -/
theorem decomp_even (hodd : KnHemi.NoOddCohomology Y) (k m : ℕ)
    (hm : 1 + 5 + m = k) (hk : Even k) (z : Hmod2 (NTop Y) k) :
    ∃ (a : Hmod2 (YTop Y) k) (b : Hmod2 (YTop Y) m),
      z = pull (prY Y) k a
        + cohCast hm (cup (cup (sig1 Y) (sig5 Y)) (pull (prY Y) m b)) := by
  subst hm
  obtain ⟨a, a₁, a₅, b, hz⟩ := decomp_top Y m z
  rw [Nat.even_iff] at hk
  have h1 : a₁ = 0 :=
    KnHemi.eq_zero_of_noOdd hodd (by rw [Nat.odd_iff]; omega) a₁
  have h5 : a₅ = 0 :=
    KnHemi.eq_zero_of_noOdd hodd (by rw [Nat.odd_iff]; omega) a₅
  refine ⟨a, b, ?_⟩
  rw [hz, h1, h5]
  simp only [pull_zero, cup_zero, cohCast_zero, add_zero, cohCast_self]

set_option maxHeartbeats 1000000 in
/-- Below total degree six there is no `t x` part at all, and in even degree the
`t`-coordinate is odd, so an even class is simply a pullback. -/
theorem decomp_even_low (hodd : KnHemi.NoOddCohomology Y) (k : ℕ) (hk : Even k)
    (hlt : k < 1 + 5) (z : Hmod2 (NTop Y) k) :
    ∃ a : Hmod2 (YTop Y) k, z = pull (prY Y) k a := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · obtain ⟨A, hA⟩ := KnHemi.kunneth_low (midBase Y) 1 0 (by omega) z
    obtain ⟨a, ha⟩ := KnHemi.kunneth_low Y 5 0 (by omega) A
    exact ⟨a, by rw [hA, ha, pull_prY_comp]⟩
  · rw [Nat.even_iff] at hk
    obtain ⟨j, hj⟩ : ∃ j, 1 + j = k := ⟨k - 1, by omega⟩
    obtain ⟨A, B, hAB⟩ := KnHemi.kunneth_decomposition (midBase Y) 1 (by omega) k j hj z
    obtain ⟨a, ha⟩ := KnHemi.kunneth_low Y 5 k (by omega) A
    obtain ⟨a₁, ha₁⟩ := KnHemi.kunneth_low Y 5 j (by omega) B
    have h1 : a₁ = 0 :=
      KnHemi.eq_zero_of_noOdd hodd (by rw [Nat.odd_iff]; omega) a₁
    refine ⟨a, ?_⟩
    rw [hAB, ha, ha₁, h1]
    simp only [pull_zero, cup_zero, cohCast_zero, add_zero]
    rw [pull_prY_comp]

set_option maxHeartbeats 1000000 in
/-- **`ChernSplit` from the parity of the degrees.**  Nothing about the Chern classes
is used beyond their degree: `γ k` lives in the even degree `2k`, so in the
four-term split its `t`- and `x`-coordinates sit in the odd degrees `2k - 1` and
`2k - 5` of `Y` and vanish. -/
def chernSplit_of_noOdd (hodd : KnHemi.NoOddCohomology Y)
    (γ : ℕ → TotalH (NTop Y)) (c : ∀ k : ℕ, Hmod2 (NTop Y) (2 * k))
    (hc : ∀ k : ℕ, γ k = TotalH.of (NTop Y) (2 * k) (c k)) :
    ChernSplit Y γ := by
  have hex : ∀ k : ℕ, ∃ (α : Hmod2 (YTop Y) (2 * k)) (β : Hmod2 (YTop Y) (2 * k - 6)),
      (2 * k < 6 → β = 0) ∧
      γ k = TotalH.map (prY Y) (TotalH.of (YTop Y) (2 * k) α)
        + Wu.tClass (prS1 Y) (sphereTopClass 1 (by omega))
          * Wu.xClass (prS5 Y) (sphereTopClass 5 (by omega))
          * TotalH.map (prY Y) (TotalH.of (YTop Y) (2 * k - 6) β) := by
    intro k
    rcases Nat.lt_or_ge (2 * k) 6 with hlt | hge
    · obtain ⟨a, ha⟩ := decomp_even_low Y hodd (2 * k) ⟨k, by omega⟩ hlt (c k)
      refine ⟨a, 0, fun _ => rfl, ?_⟩
      rw [hc, ha, map_zero, map_zero, mul_zero, add_zero, ← TotalH.map_of]
    · obtain ⟨a, b, hab⟩ := decomp_even Y hodd (2 * k) (2 * k - 6) (by omega)
        ⟨k, by omega⟩ (c k)
      refine ⟨a, b, fun h => absurd h (by omega), ?_⟩
      rw [hc, hab, map_add, totalH_of_cohCast, TotalH.of_mul, ← tClass_mul_xClass,
        ← TotalH.map_of, ← TotalH.map_of]
  choose alpha beta hbeta hsplit using hex
  exact { alpha := alpha, beta := beta, beta_low := fun k hk => hbeta k hk,
          split := hsplit }

/-- **`ChernSplit` for a degreewise family**, the shape `cc-lix-odd`'s classes come
in: `γ k` is the ring image of a class of `Hmod2 N (2 * k)`, and nothing else about
it is used. -/
def chernSplit_of_hodd (hodd : KnHemi.NoOddCohomology Y)
    (γ' : ∀ k : ℕ, Hmod2 (NTop Y) (2 * k)) :
    ChernSplit Y (fun k => TotalH.of (NTop Y) (2 * k) (γ' k)) :=
  chernSplit_of_noOdd Y hodd _ γ' (fun _ => rfl)

end KnTwo

end

end GroupApproximation.CharClass
