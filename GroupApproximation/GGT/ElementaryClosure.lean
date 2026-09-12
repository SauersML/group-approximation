import GroupApproximation.Sofic.HullSuitabilityGeometry

/-!
# The elementary closure of a loxodromic element

Osin, *Acylindrically hyperbolic groups*, Trans. AMS 368 (2016), §6, attaches to
a loxodromic element `g` of an acylindrical action the subgroup

    E(g) = { h : ∃ n ≠ 0, ∃ m ≠ 0, h gⁿ h⁻¹ = gᵐ } ,

and proves that it is the unique maximal virtually cyclic subgroup containing
`g` (Theorem 6.8), so that an element outside it moves the axis of `g` off
itself and produces a second, independent, loxodromic direction (Corollary 6.6).
That corollary is the engine of Osin's Lemma 7.1 --- an `s`-normal subgroup of a
group acting acylindrically and non-elementarily acts non-elementarily --- and
Lemma 7.1 is the geometric debt recorded by
`Manuscript.NonMF.HullFillCorrectedInputs.HullInputsCorrected.osinNonElementary`.

This module writes `E(g)` down and proves everything about it that does not need
quasi-geodesic stability.  `GGT.ElementaryOsinSNormal` then names the facts that
do need it and closes Lemma 7.1 against them.

## What is proved here

**The algebra.**  `elementaryClosure g` is a `Subgroup G` with no hypotheses at
all on `g` or on any action:

* `self_mem_elementaryClosure`, `zpowers_le_elementaryClosure` --- `g` and its
  powers lie in `E(g)`.
* `mem_elementaryClosure_of_commute` --- the centraliser of `g` lies in `E(g)`.
* `mem_elementaryClosure_conj`, `mem_elementaryClosure_conj'` --- `E(·)` is
  equivariant: `E(a g a⁻¹) = a E(g) a⁻¹`.
* `elementaryClosure_eq_of_common_zpow`, `elementaryClosure_zpow` --- `E(·)` is a
  commensurability invariant of the cyclic subgroup: a common nonzero power
  identifies the two closures, so `E(gᵏ) = E(g)` for `k ≠ 0`.

The subgroup proof is one computation.  If `a gⁿ¹ a⁻¹ = gᵐ¹` and
`b gⁿ² b⁻¹ = gᵐ²`, then conjugating `g^{n₁n₂}` by `b` gives `g^{n₁m₂}`, and
conjugating *that* by `a` gives `g^{m₁m₂}`, so `ab` carries the witness
`(n₁n₂, m₁m₂)`; and `h gⁿ h⁻¹ = gᵐ` reads backwards as `h⁻¹ gᵐ h = gⁿ`.

**The translation length.**  For a loxodromic `g` the two exponents in a witness
have the same absolute value, which is Osin's own form `h gⁿ h⁻¹ = g^{±n}`:

* `stableTranslation_congr` --- the infimum defining `stableTranslation` depends
  only on the displacement sequence, so equal displacement sequences give equal
  translation lengths.
* `stableTranslation_basepoint`, `stableTranslation_conj` --- displacement
  sequences at two basepoints differ by at most `2 d(x,y)`, and the displacement
  sequence of `a g a⁻¹` at `x` *is* the displacement sequence of `g` at `a⁻¹ x`.
  A bounded difference is invisible to the Fekete limit.
* `stableTranslation_zpow_natAbs` --- `τ(gᵏ) = |k| τ(g)`.
* `natAbs_eq_of_mem_elementaryClosure` --- `|n| τ(g) = τ(gⁿ) = τ(h gⁿ h⁻¹) =
  τ(gᵐ) = |m| τ(g)`, and `τ(g) > 0` cancels.

**The independence interface.**  Independence of two power orbits is destroyed
by a common power and, for a conjugate, by nothing else:

* `not_independent_of_common_zpow` --- if `a^p = b^q` with `p, q ≠ 0` then the two
  orbits share the points `a^{pn} x = b^{qn} x`, whose Gromov product with
  themselves is their distance to the basepoint, which is unbounded.
* `mem_elementaryClosure_of_common_zpow_conj` and its inverse form --- a common
  power of `g` and `h g^{±1} h⁻¹` is exactly a witness for `h ∈ E(g)`.
* `not_independent_conj_of_mem_elementaryClosure` --- so `h ∈ E(g)` forbids
  `Independent g (h g h⁻¹)`.  The converse is the one geometric input, and it is
  named in `GGT.ElementaryOsinSNormal`.

**The twisted intersection.**  `twistedIntersection N f` is the set
`{c : c ∈ N and f c f⁻¹ ∈ N}` that Osin's `s`-normality
(`HullSuitable.IsSNormal`) asserts to be infinite; it is a subgroup, which is
what lets the elementary-closure theory be applied to it.

## What is not proved here, and why

That `E(g)` is virtually cyclic, and that two loxodromics with no common power
are independent.  Both are Osin's Theorem 6.8 and Corollary 6.6, and both rest on
stability of quasi-geodesics: `Sofic/HullSuitabilityGeometry.lean` builds the
dyadic machinery for that argument and stops at a logarithmic bound
(`radius_le_add_clog_of_chain_avoids_ball`, `two_mul_progress_mul_far_radius_le`)
without the bootstrap to a uniform Morse constant.  They are therefore stated as
named `Prop`s in `GGT.ElementaryOsinSNormal`, with the citation attached, and
every other step of Osin's Lemma 7.1 is proved against them.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-! ## Conjugating a power -/

/-- Conjugation distributes over integer powers.  Stated in the direction the
computations below rewrite in. -/
theorem conj_zpow_eq (a y : G) (k : ℤ) : a * y ^ k * a⁻¹ = (a * y * a⁻¹) ^ k := by
  rw [conj_zpow]

/-! ## The elementary closure -/

/-- **The elementary closure of `g`** (Osin, §6): the elements conjugating some
nonzero power of `g` to some nonzero power of `g`.

For a loxodromic `g` in an acylindrical action the two exponents are forced to
agree up to sign (`natAbs_eq_of_mem_elementaryClosure`), which is Osin's own
form of the definition; the form here carries no hypothesis, so the subgroup
structure and the equivariance below are available before any geometry. -/
def elementaryClosure (g : G) : Subgroup G where
  carrier := {h : G | ∃ n m : ℤ, n ≠ 0 ∧ m ≠ 0 ∧ h * g ^ n * h⁻¹ = g ^ m}
  one_mem' := by
    show ∃ n m : ℤ, n ≠ 0 ∧ m ≠ 0 ∧ (1 : G) * g ^ n * (1 : G)⁻¹ = g ^ m
    exact ⟨1, 1, one_ne_zero, one_ne_zero, by simp⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨n₁, m₁, hn₁, hm₁, ha'⟩ := ha
    obtain ⟨n₂, m₂, hn₂, hm₂, hb'⟩ := hb
    show ∃ n m : ℤ, n ≠ 0 ∧ m ≠ 0 ∧ a * b * g ^ n * (a * b)⁻¹ = g ^ m
    refine ⟨n₁ * n₂, m₁ * m₂, mul_ne_zero hn₁ hn₂, mul_ne_zero hm₁ hm₂, ?_⟩
    have hstepb : b * g ^ (n₁ * n₂) * b⁻¹ = g ^ (n₁ * m₂) := by
      calc b * g ^ (n₁ * n₂) * b⁻¹
          = b * (g ^ n₂) ^ n₁ * b⁻¹ := by rw [← zpow_mul, mul_comm n₂ n₁]
        _ = (b * g ^ n₂ * b⁻¹) ^ n₁ := conj_zpow_eq b (g ^ n₂) n₁
        _ = (g ^ m₂) ^ n₁ := by rw [hb']
        _ = g ^ (n₁ * m₂) := by rw [← zpow_mul, mul_comm m₂ n₁]
    have hstepa : a * g ^ (n₁ * m₂) * a⁻¹ = g ^ (m₁ * m₂) := by
      calc a * g ^ (n₁ * m₂) * a⁻¹
          = a * (g ^ n₁) ^ m₂ * a⁻¹ := by rw [← zpow_mul]
        _ = (a * g ^ n₁ * a⁻¹) ^ m₂ := conj_zpow_eq a (g ^ n₁) m₂
        _ = (g ^ m₁) ^ m₂ := by rw [ha']
        _ = g ^ (m₁ * m₂) := by rw [← zpow_mul]
    calc a * b * g ^ (n₁ * n₂) * (a * b)⁻¹
        = a * (b * g ^ (n₁ * n₂) * b⁻¹) * a⁻¹ := by group
      _ = a * g ^ (n₁ * m₂) * a⁻¹ := by rw [hstepb]
      _ = g ^ (m₁ * m₂) := hstepa
  inv_mem' := by
    intro a ha
    obtain ⟨n, m, hn, hm, ha'⟩ := ha
    show ∃ n' m' : ℤ, n' ≠ 0 ∧ m' ≠ 0 ∧ a⁻¹ * g ^ n' * a⁻¹⁻¹ = g ^ m'
    refine ⟨m, n, hm, hn, ?_⟩
    rw [inv_inv, ← ha']
    group

theorem mem_elementaryClosure {g h : G} :
    h ∈ elementaryClosure g ↔
      ∃ n m : ℤ, n ≠ 0 ∧ m ≠ 0 ∧ h * g ^ n * h⁻¹ = g ^ m := Iff.rfl

/-- `g` lies in its own elementary closure. -/
theorem self_mem_elementaryClosure (g : G) : g ∈ elementaryClosure g :=
  mem_elementaryClosure.mpr ⟨1, 1, one_ne_zero, one_ne_zero, by group⟩

/-- Every power of `g` lies in `E(g)`. -/
theorem zpowers_le_elementaryClosure (g : G) :
    Subgroup.zpowers g ≤ elementaryClosure g :=
  Subgroup.zpowers_le.mpr (self_mem_elementaryClosure g)

/-- The centraliser of `g` lies in `E(g)`: a commuting element carries the
witness `(1, 1)`. -/
theorem mem_elementaryClosure_of_commute {g c : G} (hc : Commute c g) :
    c ∈ elementaryClosure g := by
  refine mem_elementaryClosure.mpr ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  rw [zpow_one, hc.eq, mul_inv_cancel_right]

/-! ## Equivariance -/

/-- `E(·)` is equivariant for conjugation. -/
theorem mem_elementaryClosure_conj {g h a : G} (hh : h ∈ elementaryClosure g) :
    a * h * a⁻¹ ∈ elementaryClosure (a * g * a⁻¹) := by
  obtain ⟨n, m, hn, hm, heq⟩ := mem_elementaryClosure.mp hh
  refine mem_elementaryClosure.mpr ⟨n, m, hn, hm, ?_⟩
  have hgn : (a * g * a⁻¹) ^ n = a * g ^ n * a⁻¹ := (conj_zpow_eq a g n).symm
  have hgm : (a * g * a⁻¹) ^ m = a * g ^ m * a⁻¹ := (conj_zpow_eq a g m).symm
  rw [hgn, hgm, ← heq]
  group

/-- The form the twisted-intersection argument consumes: an element whose
`a`-untwist lies in `E(g)` lies in `E(a g a⁻¹)`. -/
theorem mem_elementaryClosure_conj' {g y a : G}
    (hy : a⁻¹ * y * a ∈ elementaryClosure g) :
    y ∈ elementaryClosure (a * g * a⁻¹) := by
  have h := mem_elementaryClosure_conj (a := a) hy
  have h1 : a * (a⁻¹ * y * a) * a⁻¹ = y := by group
  rwa [h1] at h

/-- The reverse direction of equivariance. -/
theorem mem_elementaryClosure_of_conj_mem {g h a : G}
    (hh : a * h * a⁻¹ ∈ elementaryClosure (a * g * a⁻¹)) :
    h ∈ elementaryClosure g := by
  have hstep := mem_elementaryClosure_conj (a := a⁻¹) hh
  have h1 : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
  have h2 : a⁻¹ * (a * g * a⁻¹) * a⁻¹⁻¹ = g := by group
  rw [h1, h2] at hstep
  exact hstep

/-! ## Commensurability invariance -/

/-- An element with a nonzero power in common with `a` lies in `E(a)`: it
commutes with that common power. -/
theorem mem_elementaryClosure_of_common_zpow {a b : G} {p q : ℤ}
    (hp : p ≠ 0) (hab : a ^ p = b ^ q) : b ∈ elementaryClosure a := by
  refine mem_elementaryClosure.mpr ⟨p, p, hp, hp, ?_⟩
  rw [hab]
  group

/-- A common nonzero power makes the two elementary closures comparable. -/
theorem elementaryClosure_le_of_common_zpow {a b : G} {p q : ℤ}
    (hq : q ≠ 0) (hab : a ^ p = b ^ q) :
    elementaryClosure a ≤ elementaryClosure b := by
  intro h hh
  obtain ⟨n, m, hn, hm, heq⟩ := mem_elementaryClosure.mp hh
  refine mem_elementaryClosure.mpr
    ⟨q * n, q * m, mul_ne_zero hq hn, mul_ne_zero hq hm, ?_⟩
  have hbq : ∀ k : ℤ, b ^ (q * k) = a ^ (p * k) := by
    intro k
    rw [zpow_mul, zpow_mul, hab]
  rw [hbq n, hbq m]
  calc h * a ^ (p * n) * h⁻¹
      = h * (a ^ n) ^ p * h⁻¹ := by rw [← zpow_mul, mul_comm n p]
    _ = (h * a ^ n * h⁻¹) ^ p := conj_zpow_eq h (a ^ n) p
    _ = (a ^ m) ^ p := by rw [heq]
    _ = a ^ (p * m) := by rw [← zpow_mul, mul_comm m p]

/-- A common nonzero power identifies the two elementary closures. -/
theorem elementaryClosure_eq_of_common_zpow {a b : G} {p q : ℤ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hab : a ^ p = b ^ q) :
    elementaryClosure a = elementaryClosure b :=
  le_antisymm (elementaryClosure_le_of_common_zpow hq hab)
    (elementaryClosure_le_of_common_zpow hp hab.symm)

/-- `E(gᵏ) = E(g)` for every nonzero `k`. -/
theorem elementaryClosure_zpow (g : G) {k : ℤ} (hk : k ≠ 0) :
    elementaryClosure (g ^ k) = elementaryClosure g :=
  elementaryClosure_eq_of_common_zpow (a := g ^ k) (b := g) (p := 1) (q := k)
    one_ne_zero hk (by rw [zpow_one])

/-! ## Conjugates and common powers -/

/-- A common power of `g` and `h g h⁻¹` is a witness for `h ∈ E(g)`. -/
theorem mem_elementaryClosure_of_common_zpow_conj {g h : G} {p q : ℤ}
    (hp : p ≠ 0) (hq : q ≠ 0) (heq : g ^ p = (h * g * h⁻¹) ^ q) :
    h ∈ elementaryClosure g :=
  mem_elementaryClosure.mpr ⟨q, p, hq, hp, (conj_zpow_eq h g q).trans heq.symm⟩

/-- The same with the inverted conjugate, which is the shape the repository's
ping-pong lemma `exists_loxodromic_commutator_of_independent_conjugate` uses. -/
theorem mem_elementaryClosure_of_common_zpow_conj_inv {g h : G} {p q : ℤ}
    (hp : p ≠ 0) (hq : q ≠ 0) (heq : g ^ p = (h * g⁻¹ * h⁻¹) ^ q) :
    h ∈ elementaryClosure g := by
  refine mem_elementaryClosure.mpr ⟨-q, p, neg_ne_zero.mpr hq, hp, ?_⟩
  have hginv : (g⁻¹) ^ q = g ^ (-q) := by rw [inv_zpow, zpow_neg]
  have hc : h * g ^ (-q) * h⁻¹ = (h * g⁻¹ * h⁻¹) ^ q := by
    rw [← hginv]
    exact conj_zpow_eq h g⁻¹ q
  exact hc.trans heq.symm

/-! ## The twisted intersection -/

/-- `N ∩ f⁻¹ N f`, written with the conjugation on the element.  Osin's
`s`-normality (`HullSuitable.IsSNormal`) says exactly that this set is infinite
for every `f`; recording it as a subgroup is what lets the elementary-closure
theory be applied to it. -/
def twistedIntersection (N : Subgroup G) (f : G) : Subgroup G where
  carrier := {y : G | y ∈ N ∧ f * y * f⁻¹ ∈ N}
  one_mem' := by
    show (1 : G) ∈ N ∧ f * (1 : G) * f⁻¹ ∈ N
    refine ⟨N.one_mem, ?_⟩
    rw [mul_one, mul_inv_cancel]
    exact N.one_mem
  mul_mem' := by
    intro a b ha hb
    show a * b ∈ N ∧ f * (a * b) * f⁻¹ ∈ N
    refine ⟨N.mul_mem ha.1 hb.1, ?_⟩
    have hsplit : f * (a * b) * f⁻¹ = (f * a * f⁻¹) * (f * b * f⁻¹) := by group
    rw [hsplit]
    exact N.mul_mem ha.2 hb.2
  inv_mem' := by
    intro a ha
    show a⁻¹ ∈ N ∧ f * a⁻¹ * f⁻¹ ∈ N
    refine ⟨N.inv_mem ha.1, ?_⟩
    have hsplit : f * a⁻¹ * f⁻¹ = (f * a * f⁻¹)⁻¹ := by group
    rw [hsplit]
    exact N.inv_mem ha.2

theorem mem_twistedIntersection {N : Subgroup G} {f y : G} :
    y ∈ twistedIntersection N f ↔ y ∈ N ∧ f * y * f⁻¹ ∈ N := Iff.rfl

theorem coe_twistedIntersection (N : Subgroup G) (f : G) :
    (twistedIntersection N f : Set G) = {y : G | y ∈ N ∧ f * y * f⁻¹ ∈ N} := rfl

/-- `s`-normality, read on the twisted intersection. -/
theorem infinite_twistedIntersection {N : Subgroup G}
    (hN : HullSuitable.IsSNormal N) (f : G) :
    ((twistedIntersection N f : Subgroup G) : Set G).Infinite := by
  have h := hN f
  rwa [coe_twistedIntersection]

/-! ## Loxodromic elements have infinite order -/

/-- A nonzero power of a loxodromic element is nontrivial. -/
theorem zpow_ne_one_of_isLoxodromic {g : G} {x : X} (hg : IsLoxodromic g x)
    {j : ℤ} (hj : j ≠ 0) : g ^ j ≠ 1 := by
  intro h1
  apply hj
  have hinj : Function.Injective (fun n : ℤ => g ^ n) :=
    injective_zpow_iff_not_isOfFinOrder.mpr (not_isOfFinOrder_of_isLoxodromic hg)
  have h2 : g ^ j = g ^ (0 : ℤ) := by rw [h1, zpow_zero]
  exact hinj h2

/-- The cyclic subgroup generated by a loxodromic element is infinite. -/
theorem infinite_coe_zpowers {c : G} {x : X} (hc : IsLoxodromic c x) :
    ((Subgroup.zpowers c : Subgroup G) : Set G).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℤ => c ^ k) ?_ ?_
  · exact injective_zpow_iff_not_isOfFinOrder.mpr
      (not_isOfFinOrder_of_isLoxodromic hc)
  · intro k
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k

/-! ## Translation length is a conjugacy invariant

`stableTranslation` is defined in `Sofic/HullSuitabilityGeometry.lean` as the
infimum of `d(x, gⁿ x) / n`, and proved there to be the Fekete limit of the same
sequence.  Two facts follow from the limit form and are needed below: a bounded
perturbation of the displacement sequence does not move the limit, and the
displacement sequence of `a g a⁻¹` at `x` is that of `g` at `a⁻¹ x`. -/

/-- Equal displacement sequences give equal translation lengths.  This reads off
the infimum, with no limit theorem. -/
theorem stableTranslation_congr {g h : G} {x y : X}
    (hd : ∀ n : ℕ, dist x ((g ^ n) • x) = dist y ((h ^ n) • y)) :
    stableTranslation g x = stableTranslation h y := by
  unfold stableTranslation
  congr 1
  ext r
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, by rw [hd n]⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, by rw [hd n]⟩

/-- Inversion does not change the translation length. -/
theorem stableTranslation_inv (hiso : IsIsometricAction G X) (g : G) (x : X) :
    stableTranslation g⁻¹ x = stableTranslation g x := by
  refine stableTranslation_congr (fun n => ?_)
  have h := dist_zpow_neg (g := g) (x := x) hiso (n : ℤ)
  simpa only [zpow_neg, zpow_natCast, inv_pow] using h

/-- A displacement sequence dominated by another up to an additive constant has
a translation length dominated by the other's.  The constant is divided by `n`
and vanishes in the Fekete limit. -/
theorem stableTranslation_le_of_dist_le (hiso : IsIsometricAction G X)
    {g h : G} {x y : X} (C : ℝ)
    (hle : ∀ n : ℕ, dist x ((g ^ n) • x) ≤ dist y ((h ^ n) • y) + C) :
    stableTranslation g x ≤ stableTranslation h y := by
  have hlim : Filter.Tendsto
      (fun n : ℕ => (dist y ((h ^ n) • y) + C) / n) Filter.atTop
      (nhds (stableTranslation h y)) := by
    have hsplit : (fun n : ℕ => (dist y ((h ^ n) • y) + C) / n)
        = fun n : ℕ => dist y ((h ^ n) • y) / n + C / n := by
      funext n
      rw [add_div]
    rw [hsplit]
    have hsum := (tendsto_stableTranslation hiso h y).add
      (tendsto_const_div_atTop_nhds_zero_nat C)
    simpa only [add_zero] using hsum
  refine le_of_tendsto_of_tendsto (tendsto_stableTranslation hiso g x) hlim ?_
  filter_upwards with n
  have hinv : (0 : ℝ) ≤ ((n : ℝ))⁻¹ := by positivity
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right (hle n) hinv

/-- Translation length does not depend on the basepoint. -/
theorem stableTranslation_basepoint (hiso : IsIsometricAction G X) (g : G)
    (x y : X) : stableTranslation g x = stableTranslation g y := by
  have key : ∀ u v : X, ∀ n : ℕ,
      dist u ((g ^ n) • u) ≤ dist v ((g ^ n) • v) + 2 * dist u v := by
    intro u v n
    have h1 : dist u ((g ^ n) • u) ≤ dist u v + dist v ((g ^ n) • v)
        + dist ((g ^ n) • v) ((g ^ n) • u) :=
      le_trans (dist_triangle u v ((g ^ n) • u))
        (by linarith [dist_triangle v ((g ^ n) • v) ((g ^ n) • u)])
    have h2 : dist ((g ^ n) • v) ((g ^ n) • u) = dist v u := hiso (g ^ n) v u
    rw [h2, dist_comm v u] at h1
    linarith
  exact le_antisymm
    (stableTranslation_le_of_dist_le hiso (2 * dist x y) (key x y))
    (stableTranslation_le_of_dist_le hiso (2 * dist y x) (key y x))

/-- The displacement sequence of a conjugate, at the translated basepoint. -/
theorem dist_conj_pow (hiso : IsIsometricAction G X) (a g : G) (x : X) (n : ℕ) :
    dist x (((a * g * a⁻¹) ^ n) • x) = dist (a⁻¹ • x) ((g ^ n) • (a⁻¹ • x)) := by
  have hpow : (a * g * a⁻¹) ^ n = a * g ^ n * a⁻¹ := by rw [conj_pow]
  have h := hiso a (a⁻¹ • x) ((g ^ n) • (a⁻¹ • x))
  rw [hpow]
  simpa only [← mul_smul, mul_inv_cancel, one_smul, mul_assoc] using h

/-- Translation length is a conjugacy invariant. -/
theorem stableTranslation_conj (hiso : IsIsometricAction G X) (a g : G) (x : X) :
    stableTranslation (a * g * a⁻¹) x = stableTranslation g x := by
  have h1 : stableTranslation (a * g * a⁻¹) x = stableTranslation g (a⁻¹ • x) :=
    stableTranslation_congr (fun n => dist_conj_pow hiso a g x n)
  rw [h1, stableTranslation_basepoint hiso g (a⁻¹ • x) x]

/-- Translation length is homogeneous over the integers. -/
theorem stableTranslation_zpow_natAbs (hiso : IsIsometricAction G X) (g : G)
    (x : X) {k : ℤ} (hk : k ≠ 0) :
    stableTranslation (g ^ k) x = (k.natAbs : ℝ) * stableTranslation g x := by
  have hjpos : 0 < k.natAbs := Int.natAbs_pos.mpr hk
  rcases le_or_gt 0 k with hk0 | hk0
  · have h2 : g ^ k = g ^ k.natAbs := by
      rw [← zpow_natCast g k.natAbs, Int.natAbs_of_nonneg hk0]
    rw [h2, stableTranslation_pow hiso g x hjpos]
  · have hknat : k = -((k.natAbs : ℕ) : ℤ) := by omega
    have h2 : g ^ k = (g ^ k.natAbs)⁻¹ := by
      conv_lhs => rw [hknat]
      rw [zpow_neg, zpow_natCast]
    rw [h2, stableTranslation_inv hiso (g ^ k.natAbs) x,
      stableTranslation_pow hiso g x hjpos]

/-- **Osin's normalisation.**  A witness for membership in the elementary
closure of a loxodromic element has its two exponents equal up to sign: the
conjugation is an isometry of the axis, so it preserves translation length, and
`τ(gⁿ) = |n| τ(g)` with `τ(g) > 0`. -/
theorem natAbs_eq_of_mem_elementaryClosure (hiso : IsIsometricAction G X)
    {g h : G} {x : X} (hg : IsLoxodromic g x) {n m : ℤ}
    (hn : n ≠ 0) (hm : m ≠ 0) (heq : h * g ^ n * h⁻¹ = g ^ m) :
    n.natAbs = m.natAbs := by
  have hτ : 0 < stableTranslation g x :=
    stableTranslation_pos_of_isLoxodromic hiso hg
  have h1 : stableTranslation (h * g ^ n * h⁻¹) x
      = (n.natAbs : ℝ) * stableTranslation g x := by
    rw [stableTranslation_conj hiso h (g ^ n) x,
      stableTranslation_zpow_natAbs hiso g x hn]
  rw [heq, stableTranslation_zpow_natAbs hiso g x hm] at h1
  have h2 : ((m.natAbs : ℝ)) = ((n.natAbs : ℝ)) :=
    mul_right_cancel₀ (ne_of_gt hτ) h1
  exact_mod_cast h2.symm

/-- **Osin's form of the definition.**  For a loxodromic `g`, every element of
`E(g)` conjugates some nonzero power `gⁿ` to `g^{±n}`. -/
theorem conj_zpow_eq_or_of_mem_elementaryClosure (hiso : IsIsometricAction G X)
    {g h : G} {x : X} (hg : IsLoxodromic g x) (hh : h ∈ elementaryClosure g) :
    ∃ n : ℤ, n ≠ 0 ∧ (h * g ^ n * h⁻¹ = g ^ n ∨ h * g ^ n * h⁻¹ = g ^ (-n)) := by
  obtain ⟨n, m, hn, hm, heq⟩ := mem_elementaryClosure.mp hh
  have habs := natAbs_eq_of_mem_elementaryClosure hiso hg hn hm heq
  have hcase : n = m ∨ n = -m := by omega
  refine ⟨n, hn, ?_⟩
  rcases hcase with h1 | h1
  · left
    rw [heq, h1]
  · right
    rw [heq, h1, neg_neg]

/-- **Osin's normalisation with a positive natural exponent.**  Every element
of the elementary closure of a loxodromic element conjugates one positive power
to itself or its inverse.  Unlike the uniform exponent in DGO Corollary 6.6,
this exponent may depend on the element; no finite-index hypothesis is used.

This is the form needed to choose finite quasi-axis windows whose radius is a
positive multiple of the normalised exponent. -/
theorem exists_conj_positive_zpow_eq_or_of_mem_elementaryClosure
    (hiso : IsIsometricAction G X) {g h : G} {x : X}
    (hg : IsLoxodromic g x) (hh : h ∈ elementaryClosure g) :
    ∃ n : ℕ, 0 < n ∧
      (h * g ^ (n : ℤ) * h⁻¹ = g ^ (n : ℤ) ∨
        h * g ^ (n : ℤ) * h⁻¹ = g ^ (-(n : ℤ))) := by
  obtain ⟨k, hk, hpos | hneg⟩ :=
    conj_zpow_eq_or_of_mem_elementaryClosure hiso hg hh
  all_goals
    let n := k.natAbs
    have hn : 0 < n := Int.natAbs_pos.mpr hk
    refine ⟨n, hn, ?_⟩
  · rcases Int.natAbs_eq k with hkpos | hkneg
    · left
      change k = (n : ℤ) at hkpos
      rw [← hkpos]
      exact hpos
    · left
      change k = -(n : ℤ) at hkneg
      have hp : h * g ^ (-(n : ℤ)) * h⁻¹ = g ^ (-(n : ℤ)) := by
        rw [← hkneg]
        exact hpos
      calc
        h * g ^ (n : ℤ) * h⁻¹ = (h * g ^ (-(n : ℤ)) * h⁻¹)⁻¹ := by group
        _ = (g ^ (-(n : ℤ)))⁻¹ := by rw [hp]
        _ = g ^ (n : ℤ) := by group
  · rcases Int.natAbs_eq k with hkpos | hkneg
    · right
      change k = (n : ℤ) at hkpos
      rw [← hkpos]
      exact hneg
    · right
      change k = -(n : ℤ) at hkneg
      have hp : h * g ^ (-(n : ℤ)) * h⁻¹ = g ^ (n : ℤ) := by
        have hnk : (n : ℤ) = -k := by omega
        rw [← hkneg, hnk]
        exact hneg
      calc
        h * g ^ (n : ℤ) * h⁻¹ = (h * g ^ (-(n : ℤ)) * h⁻¹)⁻¹ := by group
        _ = (g ^ (n : ℤ))⁻¹ := by rw [hp]
        _ = g ^ (-(n : ℤ)) := by group

/-! ## Independence and common powers -/

/-- **A common nonzero power destroys independence.**  The two power orbits then
meet, at points whose Gromov product with themselves is their distance to the
basepoint, and that distance is unbounded along a loxodromic direction. -/
theorem not_independent_of_common_zpow (hiso : IsIsometricAction G X)
    {a b : G} {x : X} (ha : IsLoxodromic a x) {p q : ℤ} (hp : p ≠ 0) (_hq : q ≠ 0)
    (hab : a ^ p = b ^ q) : ¬ Independent a b x := by
  rintro ⟨C, hC⟩
  have hap : IsLoxodromic (a ^ p) x := isLoxodromic_zpow hiso ha hp
  have hev := hap.isEscaping.eventually_ge_atTop (C + 1)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have hlarge : C + 1 ≤ dist x (((a ^ p) ^ N) • x) := hN N le_rfl
  have hkey := hC (p * (N : ℤ)) (q * (N : ℤ))
  have h1 : a ^ (p * (N : ℤ)) = (a ^ p) ^ N := by
    rw [zpow_mul, zpow_natCast]
  have h2 : b ^ (q * (N : ℤ)) = (a ^ p) ^ N := by
    rw [zpow_mul, ← hab, zpow_natCast]
  rw [h1, h2, gromovProduct_self, dist_comm] at hkey
  linarith

/-- Membership in `E(g)` forbids independence from the conjugate. -/
theorem not_independent_conj_of_mem_elementaryClosure
    (hiso : IsIsometricAction G X) {g h : G} {x : X} (hg : IsLoxodromic g x)
    (hh : h ∈ elementaryClosure g) : ¬ Independent g (h * g * h⁻¹) x := by
  obtain ⟨n, m, hn, hm, heq⟩ := mem_elementaryClosure.mp hh
  refine not_independent_of_common_zpow hiso hg (p := m) (q := n) hm hn ?_
  rw [← conj_zpow_eq h g n]
  exact heq.symm

end Elementary
end GGT
end GroupApproximation
