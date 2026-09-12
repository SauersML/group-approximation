import GroupApproximation.GGT.PNaiveUniform
import GroupApproximation.GGT.PNaivePingPong
import GroupApproximation.GGT.LoxodromicCyclicEmbeddedAvoiding

/-!
# Property `P_naive` for acylindrically hyperbolic groups with trivial finite radical

Abbott--Dahmani, *Property `P_naive` for acylindrically hyperbolic groups*
(arXiv:1610.04143), Theorem 2.3: for every finite `F ⊆ G \ {1}` there is an
element `y` of infinite order such that for every `f ∈ F` the natural map
`⟨f⟩ ∗ ⟨y⟩ → G` is injective.

This module proves it on Hull's Cayley graph, with no hypothesis beyond the
group's own: acylindrical hyperbolicity and no nontrivial finite normal subgroup.

* **The partner.**  `CyclicEmbeddedChoice.exists_loxodromic_cyclic_avoiding` gives
  a loxodromic `y` with `E(y) = ⟨y⟩`, commensurable with no element of `F`, so no
  nontrivial power of any `f ∈ F` lies in `E(y)`.  A power `h₀ = y^{k₀}` has a
  strong local gap (`HullGeometry.exists_power_local_backtracking_gap`), and
  `E(h₀) = E(y)`.
* **The dichotomy.**  Every `f` is elliptic or loxodromic
  (`AcylindricalDichotomy.ellipticOrEscaping_of_isAcylindrical` and the proved
  `EscapingIsLoxodromic` at a hyperbolic acylindrical alphabet).
* **The constants.**  `PNaive.exists_uniform_regimes` gives, for each `f`, one set
  of constants for all nontrivial `g ∈ ⟨f⟩`; `F` is finite, so their sums serve
  for all of `F`.
* **The ping-pong.**  With `h = h₀ᴹ` for large `M`, transversality follows from
  `PNaive.gromovProduct_smul_le_of_bounded` / `gromovProduct_smul_le_of_far`, and
  `PNaive.injective_lift_cyclicPair` gives injectivity.

The conclusion is stated with the family `b ↦ cond b ⟨y⟩ ⟨f⟩` over `Bool`,
definitionally `NaiveFreeProduct.cyclicPairLift f y`.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra`: the geometric half of simplicity
and uniqueness of the trace of `C*_r(Q)` (tex line 1728); certifies no printed
sentence on its own.
-/

namespace GroupApproximation
namespace GGT
namespace PNaive

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **Property `P_naive`** (Abbott--Dahmani, Theorem 2.3) for an acylindrically
hyperbolic group with no nontrivial finite normal subgroup. -/
theorem naiveFreeProduct_of_isAcylindricallyHyperbolic (G : Type) [Group G]
    [IsAcylindricallyHyperbolic G]
    (hrad : ∀ N : Subgroup G, N.Normal → Finite N → N = ⊥) (F : Finset G)
    (hF : (1 : G) ∉ F) :
    ∃ y : G, (∀ k : ℤ, k ≠ 0 → y ^ k ≠ 1) ∧ ∀ f ∈ F,
      Function.Injective
        (Monoid.CoprodI.lift fun b : Bool =>
          (cond b (Subgroup.zpowers y) (Subgroup.zpowers f)).subtype) := by
  classical
  obtain ⟨A⟩ := CyclicEmbeddedChoice.nonempty_hullGeneratingSet G
  set o : Cayley A.alphabet := Cayley.base A.alphabet with hodef
  have hδ : IsHyperbolicSpace A.delta (Cayley A.alphabet) := A.hyperbolic
  have hδ0 : 0 ≤ A.delta := Elementary.nonneg_of_isHyperbolicSpace hδ o
  have hacy : IsAcylindrical G (Cayley A.alphabet) := A.acylindrical
  have hiso : IsIsometricAction G (Cayley A.alphabet) := isIsometricAction_cayley A.alphabet
  have hind : Elementary.IndependentOfNoCommonZpow G o :=
    ElementaryMorse.independentOfNoCommonZpow_cayley_of_hyperbolic A.alphabet hδ hacy
  -- the partner's root
  obtain ⟨y, hylox, hycyc, havoid, _hyemb⟩ :=
    CyclicEmbeddedChoice.exists_loxodromic_cyclic_avoiding A hrad F
  obtain ⟨k₀, hk₀, hgap₀⟩ :=
    exists_power_local_backtracking_gap hiso (add_nonneg hδ0 hδ0) hylox
  set h₀ : G := y ^ k₀ with hh₀def
  set C₀ : ℝ := gromovProduct (h₀ • o) (h₀⁻¹ • o) o with hC₀def
  have hloc : gromovProduct (h₀ • o) (h₀⁻¹ • o) o ≤ C₀ := le_refl _
  have hC₀ : 0 ≤ C₀ := gromovProduct_nonneg _ _ _
  have hturn : C₀ = gromovProduct o ((y ^ (2 * k₀)) • o) (h₀ • o) := by
    rw [hC₀def, gromovProduct_turn_eq hiso, hh₀def, ← pow_mul, mul_comm]
  have hgap : 2 * (C₀ + 2 * A.delta) < dist o (h₀ • o) := by
    rw [hturn]
    linarith
  -- no nontrivial power of an element of `F` lies in `E(h₀)`
  have hEh₀ : Elementary.elementaryClosure h₀ = Subgroup.zpowers y := by
    have hk : ((k₀ : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hk₀.ne'
    rw [hh₀def, ← zpow_natCast, Elementary.elementaryClosure_zpow y hk, hycyc]
  have hnot : ∀ f ∈ F, ∀ g ∈ Subgroup.zpowers f, g ≠ 1 →
      g ∉ Elementary.elementaryClosure h₀ := by
    intro f hf g hg hg1 hgE
    rw [hEh₀] at hgE
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact hg1 (CyclicEmbeddedChoice.pow_mem_zpowers_eq_one havoid hf a hgE)
  -- the dichotomy
  have hdich : ∀ f : G, IsElliptic f o ∨ IsLoxodromic f o := by
    intro f
    rcases AcylindricalDichotomy.ellipticOrEscaping_of_isAcylindrical hiso hacy o f with
      hell | hesc
    · exact Or.inl hell
    · exact Or.inr
        (HullSCUnionGeometry.escapingIsLoxodromic_cayley_of_acylindrical A.alphabet hδ hacy
          f hesc)
  -- the constants, per element of `F`
  have hconst : ∀ f : G, f ∈ F → ∃ (E D I : ℝ) (M₀ : ℕ), 0 ≤ E ∧ 0 ≤ D ∧ 0 ≤ I ∧
      ∀ M : ℕ, M₀ ≤ M → ∀ g ∈ Subgroup.zpowers f, g ≠ 1 →
        (dist o (g • o) ≤ E ∧
          ∀ z ∈ ({(h₀ ^ M) • o, (h₀ ^ M)⁻¹ • o} : Set (Cayley A.alphabet)),
            ∀ z' ∈ ({(h₀ ^ M) • o, (h₀ ^ M)⁻¹ • o} : Set (Cayley A.alphabet)),
              gromovProduct (g • z) z' o ≤ D) ∨
        (2 * (I + A.delta) < dist o (g • o) ∧
          ∀ z ∈ ({(h₀ ^ M) • o, (h₀ ^ M)⁻¹ • o} : Set (Cayley A.alphabet)),
            gromovProduct z (g⁻¹ • o) o ≤ I ∧ gromovProduct (g • o) z o ≤ I) := by
    intro f hf
    exact exists_uniform_regimes hδ hδ0 hiso hacy hind hloc hC₀ hgap (hdich f)
      (hnot f hf)
  choose! Ef Df If M₀f hEf hDf hIf hreg using hconst
  set E : ℝ := ∑ f ∈ F, Ef f with hEdef
  set D : ℝ := ∑ f ∈ F, Df f with hDdef
  set I : ℝ := ∑ f ∈ F, If f with hIdef
  set M₀ : ℕ := ∑ f ∈ F, M₀f f with hM₀def
  have hEle : ∀ f ∈ F, Ef f ≤ E := fun f hf =>
    Finset.single_le_sum (fun g hg => hEf g hg) hf
  have hDle : ∀ f ∈ F, Df f ≤ D := fun f hf =>
    Finset.single_le_sum (fun g hg => hDf g hg) hf
  have hIle : ∀ f ∈ F, If f ≤ I := fun f hf =>
    Finset.single_le_sum (fun g hg => hIf g hg) hf
  have hM₀le : ∀ f ∈ F, M₀f f ≤ M₀ := fun f hf =>
    Finset.single_le_sum (fun g _ => Nat.zero_le (M₀f g)) hf
  have hE0 : 0 ≤ E := Finset.sum_nonneg hEf
  have hD0 : 0 ≤ D := Finset.sum_nonneg hDf
  have hI0 : 0 ≤ I := Finset.sum_nonneg hIf
  -- the ping-pong constant and the power
  set C : ℝ := max (C₀ + 2 * A.delta) (max D I) with hCdef
  have hCturn : C₀ + 2 * A.delta ≤ C := le_max_left _ _
  have hCD : D ≤ C := le_trans (le_max_left D I) (le_max_right _ _)
  have hCI : I ≤ C := le_trans (le_max_right D I) (le_max_right _ _)
  have hκ : 0 < dist o (h₀ • o) - 2 * (C₀ + A.delta) := by linarith
  set K : ℝ := 2 * (C + A.delta) + (D + A.delta + E) + (I + A.delta) + 1 with hKdef
  obtain ⟨M₁, hM₁⟩ := exists_nat_gt (K / (dist o (h₀ • o) - 2 * (C₀ + A.delta)))
  set M : ℕ := M₀ + M₁ + 1 with hMdef
  have hM1 : 1 ≤ M := by omega
  set h : G := h₀ ^ M with hhdef
  have hstep : K < dist o (h • o) := by
    have hprog := le_dist_pow_smul hδ hδ0 hiso hloc hC₀ hgap M
    have h1 : K < (dist o (h₀ • o) - 2 * (C₀ + A.delta)) * (M₁ : ℝ) := by
      rw [div_lt_iff₀ hκ] at hM₁
      linarith
    have h2 : (dist o (h₀ • o) - 2 * (C₀ + A.delta)) * (M₁ : ℝ) ≤
        (dist o (h₀ • o) - 2 * (C₀ + A.delta)) * (M : ℝ) := by
      refine mul_le_mul_of_nonneg_left ?_ hκ.le
      rw [hMdef]
      push_cast
      linarith
    linarith
  have hlocM : gromovProduct (h • o) (h⁻¹ • o) o ≤ C :=
    le_trans (gromovProduct_turn_pow_le hδ hδ0 hiso hloc hC₀ hgap hM1) hCturn
  have hCδ : 0 ≤ C + A.delta := by linarith
  have hgapM : 2 * (C + A.delta) < dist o (h • o) := by
    rw [hKdef] at hstep
    linarith
  set ρ : ℝ := dist o (h • o) - (C + A.delta) with hρdef
  have hρD : D + A.delta + E < ρ := by
    rw [hρdef]
    rw [hKdef] at hstep
    linarith
  have hρI : I + A.delta < ρ := by
    rw [hρdef]
    rw [hKdef] at hstep
    linarith
  refine ⟨h, zpow_ne_one_of_local_gap hδ hiso hCδ hlocM hgapM, ?_⟩
  intro f hf
  have hf1 : f ≠ 1 := fun h1 => hF (h1 ▸ hf)
  refine injective_lift_cyclicPair hδ hiso hf1 hCδ hlocM hgapM ?_
  intro g hg hg1 x hx
  have hMf : M₀f f ≤ M := le_trans (hM₀le f hf) (by omega)
  -- the two ends, as members of the set `exists_uniform_regimes` quantifies over
  have hpos : h • o ∈ ({(h₀ ^ M) • o, (h₀ ^ M)⁻¹ • o} : Set (Cayley A.alphabet)) :=
    Or.inl rfl
  have hneg : h⁻¹ • o ∈ ({(h₀ ^ M) • o, (h₀ ^ M)⁻¹ • o} : Set (Cayley A.alphabet)) :=
    Or.inr rfl
  obtain ⟨z, hz, hxz⟩ : ∃ z ∈ ({(h₀ ^ M) • o, (h₀ ^ M)⁻¹ • o} : Set (Cayley A.alphabet)),
      x ∈ shadow o z ρ := by
    rcases hx with hx | hx
    · exact ⟨h • o, hpos, hx⟩
    · exact ⟨h⁻¹ • o, hneg, hx⟩
  rcases hreg f hf M hMf g hg hg1 with ⟨hgE, hgD⟩ | ⟨hgfar, hgI⟩
  · have hEg : dist o (g • o) ≤ E := le_trans hgE (hEle f hf)
    have hbound : ∀ z' ∈ ({(h₀ ^ M) • o, (h₀ ^ M)⁻¹ • o} : Set (Cayley A.alphabet)),
        gromovProduct (g • x) z' o ≤ C + A.delta := by
      intro z' hz'
      have hDz : gromovProduct (g • z) z' o ≤ D := le_trans (hgD z hz z' hz') (hDle f hf)
      have := gromovProduct_smul_le_of_bounded hδ hiso hEg hDz hρD hxz
      linarith
    exact ⟨hbound _ hpos, hbound _ hneg⟩
  · have hbound : ∀ z' ∈ ({(h₀ ^ M) • o, (h₀ ^ M)⁻¹ • o} : Set (Cayley A.alphabet)),
        gromovProduct (g • x) z' o ≤ C + A.delta := by
      intro z' hz'
      have hρf : If f + A.delta < ρ := by linarith [hIle f hf]
      have := gromovProduct_smul_le_of_far hδ hiso (hgI z hz).1 (hgI z' hz').2 hgfar hρf hxz
      linarith [hIle f hf]
    exact ⟨hbound _ hpos, hbound _ hneg⟩

end PNaive
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.PNaive.naiveFreeProduct_of_isAcylindricallyHyperbolic
