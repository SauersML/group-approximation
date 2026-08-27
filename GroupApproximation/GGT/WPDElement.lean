import GroupApproximation.Sofic.HullSuitabilityGeometry

/-!
# Weak proper discontinuity (Bestvina--Fujiwara)

This module writes down the WPD condition in the exact form Minasyan--Osin,
*Acylindrical hyperbolicity of groups acting on trees* (Math. Ann. 362 (2015),
1055--1105), Definition 3.5 states it, and in the vocabulary
`GroupApproximation.HullGeometry` already uses for actions on metric spaces.

> **Definition 3.5.**  An element `h` of a group `G` acting isometrically on a
> metric space `S` satisfies the *weak proper discontinuity* condition (or `h`
> is a *WPD element*) if for some `s ∈ S` (or, equivalently, for all `s ∈ S`)
> and every `ε ≥ 0`, there exists `M ∈ ℕ` such that
> `|PStab^ε_G({s, h^M s})| < ∞`.

Here `PStab^ε_G(A) = {g ∈ G | d(ga, a) ≤ ε for all a ∈ A}` is the *pointwise
`ε`-stabilizer* of `A` (Minasyan--Osin, §3.1, following Osin).  It is not in
general a subgroup, so it is defined here as a set.

## What is proved

* `epsStab_pair` — for a two-point set the general `ε`-stabilizer is the set
  `HullGeometry.IsAcylindrical` already quantifies over, so the WPD condition
  and acylindricity speak about literally the same sets.
* `IsWPDAt.of_basepoint` — the parenthesis of Definition 3.5: the condition at
  one basepoint gives it at every basepoint.  Moving the basepoint by `d`
  inflates `ε` by `2d`, which the `∀ ε` quantifier absorbs.
* `isWPDAt_of_isAcylindrical` — **an acylindrical action makes every loxodromic
  element WPD**.  This is the easy half of Osin's Theorem 1.2 in the direction
  `(AH₁) ⇒ (AH₃)`, and it is what keeps the WPD interface from being vacuous:
  the Cayley graph of an acylindrically hyperbolic group supplies WPD elements.
* `isWPDAt_of_cosetCover` and `isWPDAt_of_pairStab_cover` — the bookkeeping
  half of Minasyan--Osin's Corollary 4.3: an `ε`-stabilizer covered by finitely
  many translates of a finite pointwise stabilizer is finite, so a tree
  argument only has to produce the inclusion their Lemma 4.2 provides.
* `IsWPDAt.conj` — WPD is a conjugation-invariant condition.

Nothing here is a citation: Definition 3.5 is a definition, and the results
above are proved.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry

universe u v

/-! ## Pointwise `ε`-stabilizers -/

/-- **The pointwise `ε`-stabilizer** `PStab^ε_G(A)` of a subset `A` of the
space: the elements moving every point of `A` by at most `ε`.  For `ε = 0`
this is the usual pointwise stabilizer; for `ε > 0` it is in general not a
subgroup, which is why it is a `Set` here. -/
def epsStab (G : Type u) [Group G] {X : Type v} [PseudoMetricSpace X]
    [MulAction G X] (ε : ℝ) (A : Set X) : Set G :=
  {g : G | ∀ a ∈ A, dist a (g • a) ≤ ε}

/-- The pointwise `ε`-stabilizer of a **pair**, written in the shape
`HullGeometry.IsAcylindrical` quantifies over. -/
def pairStab (G : Type u) [Group G] {X : Type v} [PseudoMetricSpace X]
    [MulAction G X] (ε : ℝ) (x y : X) : Set G :=
  {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε}

section

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

theorem mem_epsStab {ε : ℝ} {A : Set X} {g : G} :
    g ∈ epsStab G ε A ↔ ∀ a ∈ A, dist a (g • a) ≤ ε :=
  Iff.rfl

theorem mem_pairStab {ε : ℝ} {x y : X} {g : G} :
    g ∈ pairStab G ε x y ↔ dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε :=
  Iff.rfl

/-- `PStab^ε_G({x,y})` is the set of elements moving both `x` and `y` by at
most `ε`. -/
theorem epsStab_pair (ε : ℝ) (x y : X) :
    epsStab G ε ({x, y} : Set X) = pairStab G ε x y := by
  ext g
  rw [mem_epsStab, mem_pairStab]
  constructor
  · intro h
    exact ⟨h x (Set.mem_insert _ _), h y (Set.mem_insert_of_mem _ rfl)⟩
  · rintro ⟨h1, h2⟩ a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha'
    · exact h1
    · rw [Set.mem_singleton_iff] at ha'
      subst ha'
      exact h2

/-- The `ε`-stabilizer grows with `ε`. -/
theorem pairStab_mono {ε ε' : ℝ} (h : ε ≤ ε') (x y : X) :
    pairStab G ε x y ⊆ pairStab G ε' x y := by
  intro g hg
  rw [mem_pairStab] at hg
  rw [mem_pairStab]
  exact ⟨le_trans hg.1 h, le_trans hg.2 h⟩

/-! ## The WPD condition -/

/-- **Weak proper discontinuity at a basepoint** (Bestvina--Fujiwara;
Minasyan--Osin, Definition 3.5).  For every `ε ≥ 0` some power `g ^ M` moves
the basepoint so far that only finitely many elements almost fix both ends. -/
def IsWPDAt {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
    [MulAction G X] (g : G) (x : X) : Prop :=
  ∀ ε : ℝ, 0 ≤ ε → ∃ M : ℕ, (pairStab G ε x ((g ^ M) • x)).Finite

/-- **`g` is a WPD element** for the action of `G` on `X`: the condition holds
at some basepoint, hence — by `IsWPDAt.of_basepoint`, under an isometric
action — at every basepoint. -/
def IsWPD (G : Type u) [Group G] (X : Type v) [PseudoMetricSpace X]
    [MulAction G X] (g : G) : Prop :=
  ∃ x : X, IsWPDAt g x

/-- **The parenthesis of Definition 3.5**: "for some `s ∈ S` (or, equivalently,
for all `s ∈ S`)".  An element moving `y` and `g ^ M • y` by at most `ε` moves
`x` and `g ^ M • x` by at most `ε + 2 d(x,y)`, and the `∀ ε` quantifier
absorbs the inflation. -/
theorem IsWPDAt.of_basepoint (hiso : IsIsometricAction G X) {g : G} {x : X}
    (h : IsWPDAt g x) (y : X) : IsWPDAt g y := by
  intro ε hε
  have hd : (0 : ℝ) ≤ dist x y := dist_nonneg
  obtain ⟨M, hM⟩ := h (ε + 2 * dist x y) (by linarith)
  refine ⟨M, hM.subset ?_⟩
  intro k hk
  rw [mem_pairStab] at hk
  obtain ⟨hk1, hk2⟩ := hk
  have hxy : dist y x = dist x y := dist_comm y x
  rw [mem_pairStab]
  refine ⟨?_, ?_⟩
  · calc dist x (k • x)
        ≤ dist x y + dist y (k • y) + dist (k • y) (k • x) :=
          dist_triangle4 x y (k • y) (k • x)
      _ = dist x y + dist y (k • y) + dist y x := by rw [hiso k y x]
      _ ≤ ε + 2 * dist x y := by rw [hxy]; linarith
  · calc dist ((g ^ M) • x) (k • (g ^ M) • x)
        ≤ dist ((g ^ M) • x) ((g ^ M) • y) +
            dist ((g ^ M) • y) (k • (g ^ M) • y) +
            dist (k • (g ^ M) • y) (k • (g ^ M) • x) :=
          dist_triangle4 _ _ _ _
      _ = dist x y + dist ((g ^ M) • y) (k • (g ^ M) • y) + dist y x := by
          rw [hiso (g ^ M) x y, hiso k ((g ^ M) • y) ((g ^ M) • x),
            hiso (g ^ M) y x]
      _ ≤ ε + 2 * dist x y := by rw [hxy]; linarith

/-- A WPD element satisfies the condition at every basepoint. -/
theorem IsWPD.isWPDAt (hiso : IsIsometricAction G X) {g : G}
    (h : IsWPD G X g) (x : X) : IsWPDAt g x := by
  obtain ⟨y, hy⟩ := h
  exact hy.of_basepoint hiso x

/-- A basepoint witnesses the WPD condition. -/
theorem IsWPDAt.isWPD {g : G} {x : X} (h : IsWPDAt g x) : IsWPD G X g :=
  ⟨x, h⟩

/-! ## Acylindrical actions -/

/-- **An acylindrical action makes every loxodromic element WPD.**

This is the implication `(AH₁) ⇒ (AH₃)` of Osin's Theorem 1.2 at the level of
a single element, and it is proved rather than cited: acylindricity bounds the
`ε`-stabilizers of *all* sufficiently distant pairs, and loxodromy produces a
power of `g` whose displacement exceeds the acylindricity radius. -/
theorem isWPDAt_of_isAcylindrical (hacy : IsAcylindrical G X) {g : G} {x : X}
    (hlox : IsLoxodromic g x) : IsWPDAt g x := by
  intro ε hε
  obtain ⟨R, N, hRN⟩ := hacy (ε + 1) (by linarith)
  obtain ⟨l, hl, B, -, hle⟩ := hlox
  obtain ⟨M, hM⟩ := exists_nat_gt ((R + B) / l)
  have hlin : R + B < l * (M : ℝ) := by
    rw [div_lt_iff₀ hl] at hM
    linarith
  have hRle : R ≤ dist x ((g ^ M) • x) := by
    have hlow := hle M
    linarith
  refine ⟨M, ((hRN x ((g ^ M) • x) hRle).1).subset ?_⟩
  intro k hk
  rw [mem_pairStab] at hk
  exact ⟨by linarith [hk.1], by linarith [hk.2]⟩

/-- **A pair of points whose stabilizers meet trivially has finite — indeed
trivial — pointwise stabilizer.**

This is the bridge between the *algebraic* input of Minasyan--Osin's criterion,
two vertex stabilizers intersecting trivially, and the *geometric* hypothesis
`PStab_G({u,v})` finite that their Corollary 4.3 consumes.  A tree argument
supplies the two stabilizer descriptions; the group theory supplies `hAB`. -/
theorem pairStab_zero_finite_of_trivial_intersection {u v : X} {A B : Subgroup G}
    (hu : ∀ k : G, dist u (k • u) ≤ 0 → k ∈ A)
    (hv : ∀ k : G, dist v (k • v) ≤ 0 → k ∈ B)
    (hAB : ∀ k : G, k ∈ A → k ∈ B → k = 1) :
    (pairStab G 0 u v).Finite := by
  refine Set.Finite.subset (Set.finite_singleton (1 : G)) ?_
  intro k hk
  rw [mem_pairStab] at hk
  rw [Set.mem_singleton_iff]
  exact hAB k (hu k hk.1) (hv k hk.2)

/-! ## The packaging step of Minasyan--Osin's Corollary 4.3 -/

/-- **A finitely-covered `ε`-stabilizer gives the WPD condition.**

Minasyan--Osin's Lemma 4.2 bounds the pointwise `ε`-stabilizer of a distant
pair by *at most `2(2ε+1)` left cosets* of the honest pointwise stabilizer of a
pair of interior points, and their Corollary 4.3 then reads off the WPD
condition.  This lemma is the bookkeeping half of that step, stated so that the
geometric half — the inclusion — is all a tree argument has to supply. -/
theorem isWPDAt_of_cosetCover {g : G} {x : X}
    (h : ∀ ε : ℝ, 0 ≤ ε → ∃ (M : ℕ) (T K : Set G), T.Finite ∧ K.Finite ∧
      pairStab G ε x ((g ^ M) • x) ⊆
        (fun p : G × G => p.1 * p.2) '' (T ×ˢ K)) :
    IsWPDAt g x := by
  intro ε hε
  obtain ⟨M, T, K, hT, hK, hsub⟩ := h ε hε
  exact ⟨M, ((hT.prod hK).image _).subset hsub⟩

/-- **Minasyan--Osin's Corollary 4.3, in the shape a tree action delivers it.**

> Let `G` be a group acting on a simplicial tree `T` and let `h ∈ G` be a
> hyperbolic element.  Suppose that for some vertices `u, v ∈ axis(h)`, the
> pointwise stabilizer `PStab_G({u,v})` is finite (the possibility `u = v` is
> allowed).  Then `h` satisfies the WPD condition.

`PStab_G({u,v})` is `pairStab G 0 u v`, the `ε = 0` case of the same family of
sets.  What a tree argument has to produce, for each `ε`, is a power `g ^ M`, a
pair `u, v` with finite pointwise stabilizer, and the finite set of translating
elements Lemma 4.2 provides. -/
theorem isWPDAt_of_pairStab_cover {g : G} {x : X}
    (h : ∀ ε : ℝ, 0 ≤ ε → ∃ (M : ℕ) (T : Set G) (u v : X), T.Finite ∧
      (pairStab G 0 u v).Finite ∧
      pairStab G ε x ((g ^ M) • x) ⊆
        (fun p : G × G => p.1 * p.2) '' (T ×ˢ pairStab G 0 u v)) :
    IsWPDAt g x := by
  refine isWPDAt_of_cosetCover fun ε hε => ?_
  obtain ⟨M, T, u, v, hT, hfin, hsub⟩ := h ε hε
  exact ⟨M, T, pairStab G 0 u v, hT, hfin, hsub⟩

/-! ## Conjugation -/

/-- Conjugation commutes with taking powers. -/
theorem pow_conj (a g : G) (n : ℕ) : (a * g * a⁻¹) ^ n = a * g ^ n * a⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, ih]
      group

/-- Conjugating the acting element and the basepoint together. -/
theorem smul_conj (a k : G) (x : X) : (a * k * a⁻¹) • (a • x) = a • (k • x) := by
  have h : a * k * a⁻¹ * a = a * k := by group
  simp only [← mul_smul, h]

/-- The `ε`-stabilizer of a translated pair is contained in the corresponding
conjugate of the `ε`-stabilizer of the pair.  Only the inclusion needed for
finiteness is proved. -/
theorem pairStab_smul_subset (hiso : IsIsometricAction G X) (ε : ℝ) (a : G)
    (x y : X) :
    pairStab G ε (a • x) (a • y) ⊆
      (fun k : G => a * k * a⁻¹) '' pairStab G ε x y := by
  intro k hk
  rw [mem_pairStab] at hk
  obtain ⟨h1, h2⟩ := hk
  have hk' : k = a * (a⁻¹ * k * a) * a⁻¹ := by group
  refine ⟨a⁻¹ * k * a, ?_, by group⟩
  rw [mem_pairStab]
  refine ⟨?_, ?_⟩
  · have h3 : dist x ((a⁻¹ * k * a) • x) = dist (a • x) (k • (a • x)) := by
      rw [← hiso a x ((a⁻¹ * k * a) • x), ← smul_conj a (a⁻¹ * k * a) x, ← hk']
    rw [h3]
    exact h1
  · have h4 : dist y ((a⁻¹ * k * a) • y) = dist (a • y) (k • (a • y)) := by
      rw [← hiso a y ((a⁻¹ * k * a) • y), ← smul_conj a (a⁻¹ * k * a) y, ← hk']
    rw [h4]
    exact h2

/-- **WPD is invariant under conjugation.** -/
theorem IsWPDAt.conj (hiso : IsIsometricAction G X) {g : G} {x : X}
    (h : IsWPDAt g x) (a : G) : IsWPDAt (a * g * a⁻¹) (a • x) := by
  intro ε hε
  obtain ⟨M, hM⟩ := h ε hε
  refine ⟨M, ?_⟩
  have hkey : ((a * g * a⁻¹) ^ M) • (a • x) = a • ((g ^ M) • x) := by
    rw [pow_conj]
    exact smul_conj a (g ^ M) x
  rw [hkey]
  exact (hM.image fun k : G => a * k * a⁻¹).subset
    (pairStab_smul_subset hiso ε a x ((g ^ M) • x))

end

end GGT
end GroupApproximation
