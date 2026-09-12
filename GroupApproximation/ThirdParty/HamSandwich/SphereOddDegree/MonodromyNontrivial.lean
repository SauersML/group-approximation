import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.DoubleCoverClass
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Nontriviality of the monodromy classifying character of the double cover

This file proves that, for `n ≥ 1`, the **monodromy classifying homomorphism**

```text
classifyingHom n x : FundamentalGroup (RP n) x →* Multiplicative (ZMod 2)
```

of the double cover `proj n : S^n → RP n` (constructed in `DoubleCoverClass.lean`)
is **surjective** — equivalently, *nontrivial*: some loop of `RP n` has monodromy
that swaps the two sheets of the cover.

This is the honest *nontriviality* statement of *Route A* toward
`α ∈ H¹(RPⁿ; F₂)`.  It does **not** require the (absent) computation `π₁(Sⁿ) = 0`
nor `SimplyConnectedSpace (Sphere n)`; it needs only that the sphere `S^n` is
**path-connected** for `n ≥ 1` (`isPathConnected_sphere`).  The geometric content
is exactly: a point `e ∈ S^n` and its antipode `-e` lie in the same path
component, so the projection of any path `e ⤳ -e` is a *loop* of `RP n` whose
monodromy sends the sheet `e` to the other sheet `-e`.

## Main declarations

* `joined_antipode` — for `n ≥ 1`, every `e : S^n` is `Joined` to its antipode `-e`.
* `projMonodromy_mk_of_lift` — the monodromy of the class of a path `γ` sends a
  fibre point `e` to the endpoint of any continuous lift of `γ` starting at `e`.
* `exists_loop_projMonodromyPerm_ne_one` — for `n ≥ 1`, some loop class at `x` has
  a nontrivial (sheet-swapping) monodromy permutation.
* `exists_classifyingHom_ne_one` — for `n ≥ 1`, some class of `π₁(RP n, x)` has
  classifying value `≠ 1`.
* `classifyingHom_surjective` — for `n ≥ 1`, `classifyingHom n x` is surjective.
-/

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory unitInterval

/--
For `n ≥ 1`, the ambient Euclidean space `ℝ^{n+1}` of `S^n` has rank `> 1`,
the hypothesis of `isPathConnected_sphere`.
-/
theorem one_lt_rank_euclidean (n : ℕ) (hn : 1 ≤ n) :
    1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
  rw [ ← Module.finrank_eq_rank, finrank_euclideanSpace_fin ] ; norm_cast;
  grind

/--
For `n ≥ 1`, every point `e : S^n` is joined by a path to its antipode `-e`
(the unit sphere of `ℝ^{n+1}` is path-connected when `n ≥ 1`).
-/
theorem joined_antipode (n : ℕ) (hn : 1 ≤ n) (e : Sphere n) : Joined e (-e) := by
  have h_path_connected : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
    apply_rules [ isPathConnected_sphere, one_lt_rank_euclidean ];
    norm_num;
  exact (h_path_connected.joinedIn e.1 e.2 (-e : Sphere n).1 (-e : Sphere n).2).joined_subtype

/--
**Monodromy via an explicit lift.**  If `Γ` is a continuous lift of the path
`γ` (i.e. `proj n ∘ Γ = γ` pointwise) starting at the fibre point `e`, then the
monodromy of the homotopy class `⟦γ⟧` sends `e` to the endpoint `Γ 1`.
-/
theorem projMonodromy_mk_of_lift (n : ℕ) {x y : RP n} (γ : Path x y)
    (e : proj n ⁻¹' {x}) (Γ : C(unitInterval, Sphere n))
    (hΓ : proj n ∘ Γ = γ) (hΓ0 : Γ 0 = (e : Sphere n)) :
    (projMonodromy n (⟦γ⟧ : Path.Homotopic.Quotient x y) e : Sphere n) = Γ 1 := by
  have hstart : γ 0 = proj n (e : Sphere n) := by
    have h0 := congrFun hΓ 0
    rw [Function.comp_apply, hΓ0] at h0
    exact h0.symm
  have h_eq : Γ = projLiftPath n γ (e : Sphere n) hstart :=
    eq_projLiftPath n γ (e : Sphere n) hstart hΓ hΓ0
  change (projLiftPath n γ (e : Sphere n) hstart) 1 = Γ 1
  exact congrArg (fun f : C(↑I, Sphere n) => f 1) h_eq.symm

/--
**A sheet-swapping loop.**  For `n ≥ 1` and any base point `x : RP n`, there
is a loop class at `x` whose monodromy permutation of the two-element fibre is
nontrivial (it swaps the two sheets of the double cover).
-/
theorem exists_loop_projMonodromyPerm_ne_one (n : ℕ) (hn : 1 ≤ n) (x : RP n) :
    ∃ γ : Path.Homotopic.Quotient x x, projMonodromyPerm n γ ≠ 1 := by
  obtain ⟨ e, rfl ⟩ := proj_surjective n x;
  -- Let `p : Path e (-e) := (joined_antipode n hn e).somePath`.
  obtain ⟨p, hp⟩ : ∃ p : Path e (-e), True := by
    exact ⟨ ( joined_antipode n hn e ).somePath, trivial ⟩;
  refine' ⟨ ⟦ ( p.map ( proj n ).continuous ).cast rfl ( proj_eq_proj_neg e ) ⟧, _ ⟩;
  intro h; have := congr_arg ( fun f => f ⟨ e, rfl ⟩ ) h; simp +decide [ projMonodromyPerm_apply ] at this;
  convert projMonodromy_mk_of_lift n ( ( p.map ( proj n ).continuous ).cast rfl ( proj_eq_proj_neg e ) ) ⟨ e, rfl ⟩ p.toContinuousMap _ _ using 1;
  · simp +decide [ this, ne_neg_self e ];
  · aesop;
  · exact p.source

/--
**Nontriviality of the classifying character.**  For `n ≥ 1` and any base
point `x : RP n`, some class of `π₁(RP n, x)` has classifying value `≠ 1`.
-/
theorem exists_classifyingHom_ne_one (n : ℕ) (hn : 1 ≤ n) (x : RP n) :
    ∃ a : FundamentalGroup (RP n) x, classifyingHom n x a ≠ 1 := by
  -- By obtain ⟨γ, hγ⟩ := exists_loop_projMonodromyPerm_ne_one n hn x
  obtain ⟨γ, hγ⟩ := exists_loop_projMonodromyPerm_ne_one n hn x;
  use FundamentalGroup.fromPath γ; simp_all +decide [ classifyingHom_eq_one_iff ] ;

/--
**Surjectivity of the monodromy classifying character.**  For `n ≥ 1`, the
classifying homomorphism `classifyingHom n x : π₁(RP n, x) → Multiplicative (ZMod 2)`
of the double cover `proj n : S^n → RP n` is surjective.  This is the honest
nontriviality statement of *Route A* toward `α ∈ H¹(RPⁿ; F₂)`.
-/
theorem classifyingHom_surjective (n : ℕ) (hn : 1 ≤ n) (x : RP n) :
    Function.Surjective (classifyingHom n x) := by
  intro g
  by_cases hg : g = 1;
  · exact ⟨ 1, hg.symm ▸ map_one _ ⟩;
  · obtain ⟨ a, ha ⟩ := exists_classifyingHom_ne_one n hn x;
    fin_cases g <;> simp_all +decide;
    exact ⟨ a, by exact Or.resolve_left ( by exact Fin.exists_fin_two.mp ⟨ _, rfl ⟩ ) ha ⟩

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
