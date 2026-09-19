import GroupApproximation.CharClass.CohomologyChartInduction

/-!
# The projection of `U × ℂP^d` below degree two

`CPSplit` speaks only about degrees two and above, so a downward induction on the
degree that peels with it bottoms out below two with nothing to stand on.  This
file is that floor, at an arbitrary fibre rather than at `ℂP^1`.

Neither half is Künneth.  Injectivity is a slice: any point of the fibre gives a
section of the projection, in *every* degree, so the pullback is split injective
with no hypothesis at all.  Surjectivity below degree two is fibre connectivity,
and it is an induction on the fibre dimension whose step is
`eq_zero_of_mvResV_eq_zero_of_lt`: below `2d+2` the restriction to the punctured
piece is injective, and degrees `0` and `1` are below that for every `d`.

The base is `ℂP^0`, which is a point, so the product is the base and
`cohProdContractible` is the whole argument.

## Main declarations

* `KnCP.cpSliceGen`, `KnCP.pull_cpFst_injective` — the slice, and injectivity in
  every degree.
* `KnCP.exists_pull_cpFst_of_lt` — surjectivity below degree two.
* `KnCP.lhLow_general` — **the floor of the ladder**, in the shape
  `cc-projective` asked for.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-! ## 1. Injectivity, in every degree -/

/-- A point of the fibre gives a section of the projection, at any rank. -/
def cpSliceGen (p : CP d) : TopCat.of U ⟶ TopCat.of (U × CP d) :=
  cmap (ContinuousMap.prodMk (ContinuousMap.id U) (ContinuousMap.const U p))

theorem cpSliceGen_comp_cpFst (p : CP d) :
    cpSliceGen U d p ≫ cpFst U d = 𝟙 (TopCat.of U) := rfl

/-- **Pullback along the projection is injective in every degree**, at any rank.
This is a section, not a Künneth statement, so it costs nothing. -/
theorem pull_cpFst_injective (k : ℕ) : Function.Injective (pull (cpFst U d) k) := by
  obtain ⟨p⟩ := nonempty_CPtop d
  intro c₁ c₂ hc
  have h := congrArg (pull (cpSliceGen U d p) k) hc
  rwa [← pull_comp, ← pull_comp, cpSliceGen_comp_cpFst, pull_id, pull_id] at h

/-! ## 2. Surjectivity below degree two -/

set_option maxHeartbeats 1000000 in
/-- **Below degree two every class is pulled back from the base**, at any rank.
The induction is on the fibre dimension; the step is the injectivity of the
restriction to the punctured piece below `2d+2`, and `0` and `1` are below that
for every `d`. -/
theorem exists_pull_cpFst_of_lt (k : ℕ) (hk : k < 2) :
    ∀ z : Hmod2 (TopCat.of (U × CP d)) k,
      ∃ a : Hmod2 (TopCat.of U) k, z = pull (cpFst U d) k a := by
  induction d with
  | zero =>
    intro z
    refine ⟨(cohProdContractible U (CP 0) k).symm z, ?_⟩
    have h := (cohProdContractible U (CP 0) k).apply_symm_apply z
    rw [cohProdContractible_apply] at h
    exact h.symm
  | succ e ih =>
    intro z
    obtain ⟨w', hw'⟩ : ∃ w', pull (cmap (punctHomotopyEquiv U e).toFun) k w'
        = (mvResV (chartU U e) (punctU U e) (cp_sup U e) k).hom z :=
      ⟨(punctPullEquiv U e k).symm _, (punctPullEquiv U e k).apply_symm_apply _⟩
    obtain ⟨a, ha⟩ := ih w'
    refine ⟨a, ?_⟩
    have hV : (mvResV (chartU U e) (punctU U e) (cp_sup U e) k).hom
        (z + pull (cpPrU U e) k a) = 0 := by
      rw [map_add, mvResV_pull_cpPrU, ← hw', ha, pull_punctHE_prU, add_self_eq_zero_two]
    have hzero := eq_zero_of_mvResV_eq_zero_of_lt U e k (by omega) _ hV
    have hcg := congrArg (fun t => t + pull (cpPrU U e) k a) hzero
    simpa only [add_assoc, add_self_eq_zero_two, add_zero, zero_add] using hcg

/-! ## 3. The interface -/

/-- **The floor of the Leray–Hirsch ladder at an arbitrary fibre.**  Pullback
along `U × ℂP^d → U` is bijective in the two degrees below two, for every base
and every rank.  This is `lhLow` with `ℂP^1` replaced by `ℂP^d`, and it uses no
Künneth statement: both halves are fibre connectivity. -/
theorem lhLow_general (n : ℕ) (hn : n < 2) : Function.Bijective (pull (cpFst U d) n) :=
  ⟨pull_cpFst_injective U d n, fun z => by
    obtain ⟨a, ha⟩ := exists_pull_cpFst_of_lt U d n hn z
    exact ⟨a, ha.symm⟩⟩

end KnCP

end

end GroupApproximation.CharClass
