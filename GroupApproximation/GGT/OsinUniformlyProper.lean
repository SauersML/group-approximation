import GroupApproximation.GGT.OsinUniformlyProperSteps

/-!
# Uniformly proper actions are not parabolic (Osin 2016, Lemma 3.4)

Osin, *Acylindrically hyperbolic groups* (arXiv:1304.1246), Lemma 3.4
(Ivanov--Olshanskii):

> A uniformly proper action on a hyperbolic space cannot be parabolic.  That is,
> if `G` is a group acting on a hyperbolic space uniformly properly with unbounded
> orbits, then `G` contains a loxodromic element.

Stated for a subgroup `K` acting on a geodesic space with the four-point
constant (`exists_loxodromic_of_uniformlyProper`).  The proof is Osin's.
Suppose no element of `K` is loxodromic.  Then at every point every element has
a large turn, by (6), and any two elements see each other in a common direction,
by (8) (`GGT/OsinUniformlyProperSteps`).

Let `A(s)` be the elements of `K` moving `s` by at most `D₀ = 26δ + 5`.  Pick `x`
with `|A(x)|` maximal and `g ∈ K` moving `x` by more than `D₀`.  Moving to the
point at distance `t₀ = 5δ + 1` along `[x, g x]` does two things.  It keeps
every element of `A(x)` in the quasi-stabilizer, by (13) for the far elements
and the triangle inequality for the near ones.  And it lowers the displacement
of `g` by at least `2` (`quasiStabilizer_step`).  After finitely many steps `g`
has joined a quasi-stabilizer containing `A(x)`, against maximality.

## Manuscript status

Infrastructure for Osin's Theorem 1.1 (the limit-set spelling of acylindrical
hyperbolicity used in `sec:torsion-free`); certifies no printed sentence on its
own.
-/

namespace GroupApproximation
namespace GGT
namespace OsinClassification

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-- **The quasi-stabilizer** of `s` in `K` at radius `D`: the elements of `K`
moving `s` by at most `D`. -/
def quasiStabilizer (K : Subgroup G) (D : ℝ) (s : X) : Set G :=
  {c : G | c ∈ K ∧ dist s (c • s) ≤ D}

/-- **One step of the Ivanov--Olshanskii iteration.**  If no element of `K` is
loxodromic and `g ∈ K` moves `y` by more than `26δ + 5`, the point at distance
`5δ + 1` from `y` on a geodesic `[y, g y]` has a larger quasi-stabilizer, and `g`
moves it by at least `2` less. -/
theorem quasiStabilizer_step {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X) {K : Subgroup G}
    (hnl : ∀ c ∈ K, ∀ s : X, ¬ IsLoxodromic c s) {g : G} (hgK : g ∈ K) {y : X}
    (hfar : 26 * δ + 5 < dist y (g • y)) :
    ∃ y' : X, quasiStabilizer K (26 * δ + 5) y ⊆ quasiStabilizer K (26 * δ + 5) y' ∧
      dist y' (g • y') ≤ dist y (g • y) - 2 := by
  have hδ0 := nonneg_delta hδ y
  have hK₀ : 2 * δ < 2 * δ + 1 := by linarith
  -- (6): every element of `K` has a large turn at `y`
  have hturn : ∀ c ∈ K,
      dist y (c • y) - (2 * δ + 1) < 2 * gromovProduct (c • y) (c⁻¹ • y) y := by
    intro c hc
    by_contra hcon
    push Not at hcon
    exact hnl c hc y (isLoxodromic_of_small_turn hδ hiso hK₀ (by linarith))
  -- (9): two elements of `K` see each other from `y` in a common direction
  have hprod : ∀ c ∈ K, ∀ d ∈ K,
      min (dist y (c • y)) (dist y (d • y)) <
        2 * gromovProduct (c • y) (d • y) y + (6 * δ + 1) := by
    intro c hc d hd
    by_contra hcon
    push Not at hcon
    have hsmall : 2 * gromovProduct (c • y) (d • y) y + ((2 * δ + 1) + 4 * δ) ≤
        min (dist y (c • y)) (dist y (d • y)) := by linarith
    have h2 := two_mul_gromovProduct_inv_le hδ (hturn c hc) (hturn d hd) hsmall
    have h1 : 2 * gromovProduct (c • y) (d • y) y + (2 * δ + 1) ≤
        min (dist y (c • y)) (dist y (d • y)) := by linarith
    exact hnl (c⁻¹ * d) (K.mul_mem (K.inv_mem hc) hd) y
      (isLoxodromic_inv_mul_of_small_products hδ hiso hK₀ h1 h2)
  obtain ⟨p, hp, hp0, hp1⟩ := hgeo y (g • y)
  have hyp : dist y (p (5 * δ + 1)) = 5 * δ + 1 := by
    have h := hp 0 ⟨le_rfl, dist_nonneg⟩ (5 * δ + 1) ⟨by linarith, by linarith⟩
    rw [hp0] at h
    rw [h, zero_sub, abs_neg, abs_of_nonneg (by linarith)]
  refine ⟨p (5 * δ + 1), ?_, ?_⟩
  · rintro c ⟨hcK, hcD⟩
    refine ⟨hcK, ?_⟩
    by_cases hc : 16 * δ + 3 ≤ dist y (c • y)
    · -- a far element: the displacement estimate (13)
      have hinv : dist y (c⁻¹ • y) = dist y (c • y) := PNaive.dist_inv_smul hiso c y
      have hq1 := hprod g hgK c hcK
      have hq2 := hprod g hgK c⁻¹ (K.inv_mem hcK)
      rw [hinv] at hq2
      have hmin : 16 * δ + 3 ≤ min (dist y (g • y)) (dist y (c • y)) :=
        le_min (by linarith) hc
      have hest := dist_smul_geodesicPoint_le hδ hδ0 hgeo hiso (g := g) (h := c)
        (t₀ := 5 * δ + 1) hp hp0 hp1 (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith)
      linarith
    · -- a near element: the triangle inequality
      push Not at hc
      have h1 := dist_triangle (p (5 * δ + 1)) y (c • p (5 * δ + 1))
      have h2 := dist_triangle y (c • y) (c • p (5 * δ + 1))
      have h3 : dist (c • y) (c • p (5 * δ + 1)) = dist y (p (5 * δ + 1)) := hiso c _ _
      rw [dist_comm (p (5 * δ + 1)) y] at h1
      linarith
  · -- `g` itself moves the new point less
    have hg6 := hturn g hgK
    have hself : gromovProduct (g • y) (g • y) y = dist (g • y) y := gromovProduct_self _ _
    have hest := dist_smul_geodesicPoint_le hδ hδ0 hgeo hiso (g := g) (h := g)
      (t₀ := 5 * δ + 1) hp hp0 hp1 (by linarith) (by linarith) (by linarith)
      (by rw [hself, dist_comm]; linarith) (by linarith)
    linarith

/-- **Osin's Lemma 3.4 (Ivanov--Olshanskii), subgroup form.**  If a subgroup `K`
acts uniformly properly on a geodesic hyperbolic space and its orbit of `x` is
unbounded, then `K` contains a loxodromic element. -/
theorem exists_loxodromic_of_uniformlyProper {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X) {K : Subgroup G}
    (hup : ∀ ε : ℝ, ∃ N : ℕ, ∀ s : X,
      (quasiStabilizer K ε s).Finite ∧ (quasiStabilizer K ε s).ncard ≤ N)
    {x : X} (hunb : ¬ ∃ B : ℝ, ∀ c ∈ K, dist x (c • x) ≤ B) :
    ∃ c ∈ K, IsLoxodromic c x := by
  classical
  by_contra hno
  push Not at hno
  have hnl : ∀ c ∈ K, ∀ s : X, ¬ IsLoxodromic c s := fun c hc s hs =>
    hno c hc (isLoxodromic_of_isLoxodromic hiso hs)
  have hδ0 := nonneg_delta hδ x
  obtain ⟨N, hN⟩ := hup (26 * δ + 5)
  -- the largest quasi-stabilizer
  have hex : ∃ m : ℕ, ∀ s : X, (quasiStabilizer K (26 * δ + 5) s).ncard ≤ m :=
    ⟨N, fun s => (hN s).2⟩
  have hm : ∀ s : X, (quasiStabilizer K (26 * δ + 5) s).ncard ≤ Nat.find hex :=
    Nat.find_spec hex
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : X, Nat.find hex ≤ (quasiStabilizer K (26 * δ + 5) x₀).ncard := by
    by_contra hall
    push Not at hall
    have hlow : ∀ s : X, (quasiStabilizer K (26 * δ + 5) s).ncard ≤ Nat.find hex - 1 :=
      fun s => by have := hall s; omega
    have hle := Nat.find_min' hex hlow
    have hpos : 0 < Nat.find hex := by
      have := hall x
      omega
    omega
  -- an element moving `x₀` far
  obtain ⟨g, hgK, hgfar⟩ : ∃ g ∈ K, 26 * δ + 5 < dist x₀ (g • x₀) := by
    by_contra hb
    push Not at hb
    apply hunb
    refine ⟨26 * δ + 5 + 2 * dist x x₀, fun c hc => ?_⟩
    have h1 := dist_triangle x x₀ (c • x)
    have h2 := dist_triangle x₀ (c • x₀) (c • x)
    have h3 : dist (c • x₀) (c • x) = dist x₀ x := hiso c x₀ x
    have h4 := hb c hc
    rw [dist_comm x₀ x] at h3
    linarith
  -- the iteration
  have hiter : ∀ n : ℕ, ∃ y : X,
      quasiStabilizer K (26 * δ + 5) x₀ ⊆ quasiStabilizer K (26 * δ + 5) y ∧
        (dist y (g • y) ≤ 26 * δ + 5 ∨ dist y (g • y) ≤ dist x₀ (g • x₀) - 2 * n) := by
    intro n
    induction n with
    | zero => exact ⟨x₀, subset_rfl, Or.inr (by simp)⟩
    | succ n ih =>
        obtain ⟨y, hsub, hy⟩ := ih
        by_cases hyD : dist y (g • y) ≤ 26 * δ + 5
        · exact ⟨y, hsub, Or.inl hyD⟩
        · push Not at hyD
          obtain ⟨y', hsub', hdec⟩ := quasiStabilizer_step hδ hgeo hiso hnl hgK hyD
          refine ⟨y', hsub.trans hsub', Or.inr ?_⟩
          rcases hy with hy | hy
          · linarith
          · push_cast
            linarith
  obtain ⟨y, hsub, hy⟩ := hiter ⌈dist x₀ (g • x₀) / 2⌉₊
  have hgy : dist y (g • y) ≤ 26 * δ + 5 := by
    rcases hy with hy | hy
    · exact hy
    · have hceil := Nat.le_ceil (dist x₀ (g • x₀) / 2)
      linarith
  -- the count
  have hgA : g ∈ quasiStabilizer K (26 * δ + 5) y := ⟨hgK, hgy⟩
  have hgnot : g ∉ quasiStabilizer K (26 * δ + 5) x₀ := fun h => by
    have := h.2
    linarith
  have hins : insert g (quasiStabilizer K (26 * δ + 5) x₀) ⊆
      quasiStabilizer K (26 * δ + 5) y := Set.insert_subset hgA hsub
  have hcard := Set.ncard_le_ncard hins (hN y).1
  rw [Set.ncard_insert_of_notMem hgnot (hN x₀).1] at hcard
  have := hm y
  omega

end OsinClassification
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.OsinClassification.quasiStabilizer_step
#audit_axioms GroupApproximation.GGT.OsinClassification.exists_loxodromic_of_uniformlyProper
