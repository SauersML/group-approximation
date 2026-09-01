import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Final.OddDegreeTheoremUnconditional
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.DegreeAPIStrengthening
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereHomologyMVStep
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularHomologyHomotopyInvariance
import Mathlib

/-!
# The Borsuk–Ulam theorem

Building on the project's unconditional odd-degree theorem
(`odd_degree_of_odd_sphere_self_map_unconditional`: an antipode-preserving self-map
of `Sⁿ` has odd, hence nonzero, degree) we prove the **Borsuk–Ulam theorem**.

## Strategy

The key bridge is:

* **A non-surjective self-map of `Sⁿ` has degree `0`** (`degreeOfIso_eq_zero_of_not_surjective`).
  If `f` misses a point `p`, it factors through the complement `Sⁿ ∖ {p}`, which is
  contractible (stereographic projection), so `f` is nullhomotopic and its degree is `0`
  by homotopy invariance and `degreeOfIso_const`.

* **No odd map `Sⁿ⁺¹ → Sⁿ`** (`no_odd_map_sphere_succ`).  Compose a hypothetical odd
  `g : Sⁿ⁺¹ → Sⁿ` with the (odd) equatorial inclusion `equatorIncl n : Sⁿ ↪ Sⁿ⁺¹`.
  The composite is an odd self-map of `Sⁿ⁺¹`, so it has odd (nonzero) degree; but it
  misses the north pole, so it has degree `0`. Contradiction.

* **Borsuk–Ulam, ℝⁿ form** (`borsuk_ulam`): every continuous `f : Sⁿ⁺¹ → ℝⁿ⁺¹` has a
  point `x` with `f x = f (-x)`.  Otherwise `x ↦ (f x - f (-x)) / ‖f x - f (-x)‖` would
  be an odd map `Sⁿ⁺¹ → Sⁿ`, contradicting `no_odd_map_sphere_succ`.
-/

noncomputable section

open CategoryTheory Limits AlgebraicTopology Metric

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## Complement of a point in the sphere is contractible -/

/-
For any point `p` on `Sⁿ`, the complement `Sⁿ ∖ {p}` is contractible, via
stereographic projection centred at `p`.
-/
theorem contractibleSpace_sphere_compl_point (n : ℕ) (p : Sphere n) :
    ContractibleSpace ({p}ᶜ : Set (Sphere n)) := by
  let hnorm : ‖(p.val : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simp [norm_eq_of_mem_sphere p]
  letI : ContractibleSpace ((stereographic hnorm).target) := by
    rw [stereographic_target]
    exact Homeomorph.contractibleSpace (Homeomorph.Set.univ _)
  have hsource : ({p}ᶜ : Set (Sphere n)) = (stereographic hnorm).source := by
    rw [stereographic_source]
  exact Homeomorph.contractibleSpace
    ((Homeomorph.setCongr hsource).trans (stereographic hnorm).toHomeomorphSourceTarget)

/-! ## A non-surjective self-map has degree zero -/

/-
**A non-surjective continuous self-map of `Sⁿ` (`n ≥ 1`) has degree `0`.**
It factors through the complement of a missed point, which is contractible, so it is
nullhomotopic; homotopy invariance and `degreeOfIso_const` give degree `0`.
-/
theorem degreeOfIso_eq_zero_of_not_surjective {n : ℕ} (hn : n ≠ 0)
    (e : SphereTopHomologyIso n) (f : C(Sphere n, Sphere n))
    (hf : ¬ Function.Surjective f) :
    degreeOfIso e f = 0 := by
  -- By `¬ Function.Surjective f` obtain a point `p : Sphere n` with `p ∉ Set.range f`, so `∀ x, f x ≠ p`, equivalently `∀ x, f x ∈ ({p}ᶜ : Set (Sphere n))`.
  obtain ⟨p, hp⟩ : ∃ p : Sphere n, ∀ x, f x ≠ p := by
    simp_all +decide [ Function.Surjective ];
  -- Let `S := ({p}ᶜ : Set (Sphere n))`. By `contractibleSpace_sphere_compl_point n p`, `S` is a `ContractibleSpace` (add it as a `haveI`).
  letI : ContractibleSpace {x : Sphere n | x ≠ p} := by
    change ContractibleSpace ({p}ᶜ : Set (Sphere n))
    exact contractibleSpace_sphere_compl_point n p
  -- Define the corestriction `f' : C(Sphere n, {p}ᶜ)` by `f' x = ⟨f x, hx⟩` where `hx : f x ∈ {p}ᶜ`.
  set f' : C(Sphere n, {x : Sphere n | x ≠ p}) := ⟨fun x => ⟨f x, hp x⟩, by
    exact Continuous.subtype_mk f.continuous _⟩
  generalize_proofs at *;
  -- Because `S` is contractible, `ContinuousMap.id S` is nullhomotopic: `id_nullhomotopic S` gives `y : S` with `ContinuousMap.Homotopic (ContinuousMap.id S) (ContinuousMap.const S y)`.
  obtain ⟨y, hy⟩ : ∃ y : {x : Sphere n | x ≠ p}, ContinuousMap.Homotopic (ContinuousMap.id {x : Sphere n | x ≠ p}) (ContinuousMap.const {x : Sphere n | x ≠ p} y) := by
    exact id_nullhomotopic _
  -- Right-compose this homotopy with `f'` (using `ContinuousMap.Homotopic.hcomp`/`ContinuousMap.Homotopic.comp`) to get `Homotopic ((ContinuousMap.id S).comp f') ((ContinuousMap.const S y).comp f')`, i.e. `Homotopic f' (ContinuousMap.const (Sphere n) y)` after simplifying `id.comp f' = f'` and `(const _ y).comp f' = const _ y`.
  have h_homotopic : ContinuousMap.Homotopic f' (ContinuousMap.const (Sphere n) y) := by
    simpa using hy.comp (ContinuousMap.Homotopic.refl f')
  -- Left-compose with `incl` to get `Homotopic (incl.comp f') (incl.comp (const _ y))`, and `incl.comp (const _ y) = ContinuousMap.const (Sphere n) (incl y)`.
  have h_homotopic_incl : ContinuousMap.Homotopic f (ContinuousMap.const (Sphere n) y.val) := by
    obtain ⟨ H, hH ⟩ := h_homotopic;
    refine' ⟨ _, _, _ ⟩;
    exact ContinuousMap.mk ( fun x => H x |>.1 ) ( by continuity ); all_goals aesop;
  rw [ degreeOfIso_eq_of_homotopic singularPrismOperator e h_homotopic_incl, degreeOfIso_const e hn ]

/-! ## The odd equatorial inclusion `Sⁿ ↪ Sⁿ⁺¹` -/

/-- The equatorial inclusion `Sⁿ ↪ Sⁿ⁺¹`, prepending a zero coordinate (the map
`gFun`).  Its image avoids the north pole, and it is antipode-preserving. -/
def equatorIncl (n : ℕ) : C(Sphere n, Sphere (n + 1)) :=
  ⟨fun y => ⟨gFun n y, gFun_mem_sphere n y⟩,
    continuous_subtype_val.comp (continuous_gFun n)⟩

@[simp]
theorem equatorIncl_apply (n : ℕ) (y : Sphere n) :
    (equatorIncl n y).val = gFun n y := rfl

/-
The equatorial inclusion is antipode-preserving (odd).
-/
theorem equatorIncl_odd (n : ℕ) (y : Sphere n) :
    equatorIncl n (-y) = - equatorIncl n y := by
  ext i; induction i using Fin.inductionOn <;> simp +decide [ * ] ;
  · unfold gFun; aesop;
  · unfold gFun; aesop;

/-
The north pole is not in the image of the equatorial inclusion.
-/
theorem northPole_not_mem_range_equatorIncl (n : ℕ) (y : Sphere n) :
    equatorIncl n y ≠ northPole n := by
  simpa [equatorIncl, sphereBand, upperPunctured] using (gFun_mem_band n y).1

/-! ## No odd map `Sⁿ⁺¹ → Sⁿ` -/

/-
**Borsuk–Ulam (odd-map form).** There is no antipode-preserving continuous map
`Sⁿ⁺¹ → Sⁿ`.
-/
theorem no_odd_map_sphere_succ (n : ℕ) (g : C(Sphere (n + 1), Sphere n))
    (hg : ∀ x, g (-x) = - g x) : False := by
  by_contra h_g;
  convert @odd_degree_of_odd_sphere_self_map_unconditional ( n + 1 ) ( by omega ) ( ( equatorIncl n ).comp g ) ?_ using 1;
  · rw [ degreeOfIso_eq_zero_of_not_surjective ] <;> norm_num;
    exact fun h => northPole_not_mem_range_equatorIncl n ( g ( Classical.choose ( h ( northPole n ) ) ) ) ( by simpa using Classical.choose_spec ( h ( northPole n ) ) );
  · intro x; exact (by
    exact equatorIncl_odd n _ ▸ by simp +decide [ hg ] ;)

/-! ## The Borsuk–Ulam theorem, ℝⁿ form -/

/-
**The Borsuk–Ulam theorem.** For every continuous map `f : Sⁿ⁺¹ → ℝⁿ⁺¹` there is
a point `x` with `f x = f (-x)`.
-/
theorem borsuk_ulam {n : ℕ}
    (f : C(Sphere (n + 1), EuclideanSpace ℝ (Fin (n + 1)))) :
    ∃ x : Sphere (n + 1), f x = f (-x) := by
  by_contra! h;
  -- Define `v x := f x - f (-x)`; then `v x ≠ 0` since `f x ≠ f (-x)`, so `‖v x‖ ≠ 0`.
  set v : Sphere (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) := fun x => f x - f (-x)
  have hv : ∀ x, v x ≠ 0 := by
    exact fun x => sub_ne_zero_of_ne <| h x;
  -- Define `g : C(Sphere (n+1), Sphere n)` by `g x = ⟨‖v x‖⁻¹ • v x, hmem x⟩` where
  -- `hmem x : ‖v x‖⁻¹ • v x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1`.
  set g : C(Sphere (n + 1), Sphere n) := ⟨fun x => ⟨‖v x‖⁻¹ • v x, by
    simp +decide [ norm_smul, hv ]⟩, by
    exact Continuous.subtype_mk ( Continuous.smul ( Continuous.inv₀ ( continuous_norm.comp <| by exact Continuous.sub ( f.continuous ) <| f.continuous.comp <| continuous_neg ) fun x => norm_ne_zero_iff.mpr <| hv x ) <| by exact Continuous.sub ( f.continuous ) <| f.continuous.comp <| continuous_neg ) _⟩
  generalize_proofs at *;
  apply no_odd_map_sphere_succ n g;
  intro x; ext; simp [g, v];
  rw [ norm_sub_rev ] ; ring

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
