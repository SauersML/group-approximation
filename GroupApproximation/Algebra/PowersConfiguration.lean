import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Common

/-!
# Powers' configuration: the combinatorial interface

Powers' averaging argument asks, for a finite `F ⊆ G` avoiding `1` and a count
`n`, for a partition `G = C ⊔ D` together with `n` elements such that

* `f • C` is disjoint from `C` for every `f ∈ F`, and
* the translates `gᵢ • D` are pairwise disjoint.

`IsPowersConfig F n` below is exactly that conjunction, for one `F` and one `n`;
the Powers property of a group is its universal quantification, which lives with
the analytic consequence and is not imported here.

## What this module fixes

The two clauses pull in opposite directions and it is easy to get the shape
backwards.  `f • C ∩ C = ∅` for a nontrivial `f` forces `C` to be *wandering*,
hence small; `D` is then its co-small complement, and "`n` disjoint translates
of `D`" is not a smallness statement about `D` at all.  Unfolding it,

```
Disjoint (gᵢ • Cᶜ) (gⱼ • Cᶜ)   ↔   (gᵢ⁻¹ gⱼ) • Cᶜ ⊆ C
```

the translate of the *complement* of `C` must land **inside** `C`.  That is
extreme proximality, and it is what a large power of a loxodromic element
supplies: `hᵐ` pushes the complement of a neighbourhood of the two fixed points
into a neighbourhood of one of them, the attracting one for `m > 0` and the
repelling one for `m < 0`.  Both signs occur as `i` and `j` range over `Fin n`,
which is why the wandering set has to surround *both* fixed points.

`disjoint_smul_compl` is that identity, and `isPowersConfig_of_cone` is the
resulting criterion: one set and one element, with a wandering hypothesis and a
proximality hypothesis, produce the whole configuration with `gᵢ = hⁱ`.  Any
construction — free-group cones by reduced words, or cones around the fixed
points of a loxodromic in a hyperbolic space — meets the interface here.

`isPowersConfig_of_mulEquiv` transports a configuration along a group
isomorphism, so an instance proved on a concrete model applies to every group
isomorphic to it.
-/

namespace GroupApproximation
namespace PowersConfig

open scoped Pointwise

universe u v

variable {G : Type u} [Group G]

/-- **Powers' four clauses** for one finite set `F` and one count `n`: a
partition `G = C ⊔ D` with `C` wandering under `F`, and `n` elements whose
translates of `D` are pairwise disjoint. -/
def IsPowersConfig (F : Finset G) (n : ℕ) : Prop :=
  ∃ (C D : Set G) (g : Fin n → G),
    Disjoint C D ∧ C ∪ D = Set.univ ∧
      (∀ f ∈ F, Disjoint (f • C) C) ∧
        (∀ i j, i ≠ j → Disjoint (g i • D) (g j • D))

/-! ## Disjoint translates of a complement -/

/-- **Disjoint translates of `Cᶜ` are extreme proximality.**  If `a⁻¹b` carries
the complement of `C` into `C`, then `a • Cᶜ` and `b • Cᶜ` are disjoint. -/
theorem disjoint_smul_compl (C : Set G) {a b : G}
    (h : (a⁻¹ * b) • Cᶜ ⊆ C) : Disjoint (a • Cᶜ) (b • Cᶜ) := by
  refine Set.disjoint_left.mpr ?_
  intro x hxa hxb
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hxa hxb
  have hmem : (a⁻¹ * b) • (b⁻¹ • x) ∈ C := h (Set.smul_mem_smul_set hxb)
  have hval : (a⁻¹ * b) • (b⁻¹ • x) = a⁻¹ • x := by
    rw [smul_smul, mul_assoc, mul_inv_cancel, mul_one]
  rw [hval] at hmem
  exact hxa hmem

/-! ## The criterion -/

/-- **One wandering set and one proximal element give Powers' configuration.**

`C` is the wandering set — in the intended examples a neighbourhood of the two
fixed points of `h` — and `hᵐ` carries `Cᶜ` into `C` for every nonzero exponent
of size less than `n`.  The configuration is `D = Cᶜ` and `gᵢ = hⁱ`. -/
theorem isPowersConfig_of_cone {F : Finset G} {n : ℕ} (C : Set G) (h : G)
    (hwander : ∀ f ∈ F, Disjoint (f • C) C)
    (hprox : ∀ m : ℤ, m ≠ 0 → m.natAbs < n → (h ^ m) • Cᶜ ⊆ C) :
    IsPowersConfig F n := by
  refine ⟨C, Cᶜ, fun i => h ^ (i : ℕ), disjoint_compl_right,
    Set.union_compl_self C, hwander, ?_⟩
  intro i j hij
  have hne : (i : ℕ) ≠ (j : ℕ) := fun hc => hij (Fin.val_injective hc)
  have hi := i.isLt
  have hj := j.isLt
  have hpow : ((h ^ (i : ℕ))⁻¹ * h ^ (j : ℕ))
      = h ^ (-((i : ℕ) : ℤ) + ((j : ℕ) : ℤ)) := by
    rw [zpow_add, zpow_neg, zpow_natCast, zpow_natCast]
  refine disjoint_smul_compl C ?_
  rw [hpow]
  exact hprox _ (by omega) (by omega)

/-! ## Transport along an isomorphism -/

/-- Preimages of translates under a group isomorphism. -/
theorem preimage_smul_mulEquiv {H : Type v} [Group H] (φ : G ≃* H) (a : G)
    (S : Set H) : a • (φ ⁻¹' S) = φ ⁻¹' ((φ a) • S) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul,
    map_mul, map_inv]

/-- **A Powers configuration transports along a group isomorphism.**  `F'` need
only contain the image of `F`. -/
theorem isPowersConfig_of_mulEquiv {H : Type v} [Group H] (φ : G ≃* H)
    {F : Finset G} {F' : Finset H} (hF : ∀ f ∈ F, φ f ∈ F') {n : ℕ}
    (hH : IsPowersConfig F' n) : IsPowersConfig F n := by
  obtain ⟨C, D, g, hCD, hunion, hwander, htrans⟩ := hH
  refine ⟨φ ⁻¹' C, φ ⁻¹' D, fun i => φ.symm (g i), hCD.preimage _, ?_, ?_, ?_⟩
  · rw [← Set.preimage_union, hunion, Set.preimage_univ]
  · intro f hf
    rw [preimage_smul_mulEquiv]
    exact (hwander (φ f) (hF f hf)).preimage _
  · intro i j hij
    rw [preimage_smul_mulEquiv, preimage_smul_mulEquiv,
      MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact (htrans i j hij).preimage _

end PowersConfig
end GroupApproximation
