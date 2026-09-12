import GroupApproximation.KOne.AllRanksElementaryCore
import GroupApproximation.Leavitt.PrefixCode
import GroupApproximation.Leavitt.UniversalLeavitt
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Module.LinearMap.End

/-!
# `H ≅ GL_n(R) = EL_n(R)` at every `n ≥ 2`, and the right-module self-similarity `R ≅ R ⊕ R`

`non_mf_groups_exist.tex`:

* Introduction (line ~156–157): "The right module `R_R` over `R = L_{𝔽₂}(1,2)`
  satisfies `R_R ≅ R_R ⊕ R_R`, and `H` is its automorphism group;
  Khanh--Thanh show that `H ≅ GL_n(R) = EL_n(R)` for every `n ≥ 2`"
  (Khanh--Thanh, Proposition 4.2 and Corollary 4.4).
* "The binary example" (line ~1117–1119): "the maps `x ↦ (t₀x,t₁x)` and
  `(y,z) ↦ s₀y+s₁z` are mutually inverse isomorphisms of right `R`-modules
  between `R` and `R ⊕ R`, and `H ≅ GL₄(R) = EL₄(R)`."

`Manuscript/OneSidedMFRadical/UnitGroupHeadline.lean` already proves the whole
of `thm:headline` — including `H ≅ GL₄(R) = EL₄(R)` — at the one rank the rest
of the manuscript actually uses, `n = 4`.  This module supplies what the two
sentences above assert *beyond* that one rank, and in a form that carries the
manuscript's literal objects rather than only the consequence for `Rˣ`:

* `LeavittFamily.rightLinearEquivSquare` is the printed pair of maps
  `x ↦ (t₀x, t₁x)`, `(y,z) ↦ s₀y+s₁z`, bundled as a `LinearEquiv` over `Aᵐᵒᵖ`
  — Mathlib's spelling of "isomorphism of right `A`-modules"
  (`Semiring.toOppositeModule : Module Aᵐᵒᵖ A` reads `c • x` as `x * c.unop`,
  i.e. right multiplication by `c.unop`) — for an arbitrary ring carrying a
  `LeavittFamily`.  `LeavittModuleRank.lean` already has the *left*-module
  mirror of this, `LeavittFamily.linearEquivSquare` (`x ↦ (xs₀,xs₁)`), and its
  docstring flags the right-module pairing used here as "both readings are
  true" but not formalized there; this module closes that gap.
* `LeavittFamily.nonempty_prefixUnitsEquiv` upgrades the self-similarity
  `Θ_C : M_r(A) ≅ A` of `PrefixCode.lean` from the four-leaf code used by
  `UnitGroupHeadline` to *every* leaf count `m ≥ 1`, via the left-comb code
  `leftCombCode (m - 1) = {0, 10, 110, …, 1^{m-2}0, 1^{m-1}}`.
* Combined with `BinaryLeavitt.elementaryGroup_eq_top` (`GLₙ = ELₙ` for every
  `n ≥ 2`, already in the tree), this gives `Rˣ ≅ ELₙ(R)` for every `n ≥ 2` —
  the Introduction's printed claim at every rank, not only `n = 4`.
* `unitsEquivEndUnits` is the Introduction's "`H` is its automorphism group"
  clause, `Rˣ ≅ Aut_R(R_R) = (\operatorname{End}_R(R_R))^\times`, for `R_R`
  the ring viewed as a right module over itself.  It is the general fact
  `RingEquiv.moduleEndSelfOp : R ≃+* Module.End Rᵐᵒᵖ R` (left multiplication
  is the full endomorphism ring of the regular right module — already in
  Mathlib) carried to units; it needs no `LeavittFamily` at all.

Nothing here is assumed: `BinaryLeavitt.elementaryGroup_eq_top`,
`PrefixCode.leftCombCode_complete`, and `RingEquiv.moduleEndSelfOp` are all
proved theorems (the last is Mathlib's), and the Khanh--Thanh citation is
attribution, exactly as `UnitGroupHeadline.lean` documents for the `n = 4`
case.
-/

namespace GroupApproximation

/-! ## `Rˣ ≅ Aut_R(R_R)`, for an arbitrary ring -/

/-- **The printed clause "`H` is its automorphism group"**: `Aˣ ≅
(\operatorname{End}_A(A_A))^\times`, the units of the (right-`A`-linear)
endomorphism ring of `A` viewed as a right module over itself.  Every
`A`-linear endomorphism of the regular right module is left multiplication by
a fixed element (`RingEquiv.moduleEndSelfOp`, Mathlib), so this needs no
`LeavittFamily` and holds for every ring. -/
def unitsEquivEndUnits (A : Type*) [Ring A] :
    Aˣ ≃* (Module.End Aᵐᵒᵖ A)ˣ :=
  Units.mapEquiv (RingEquiv.moduleEndSelfOp A).toMulEquiv

/-! ## The right-module self-similarity, for an arbitrary `LeavittFamily` -/

namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- `s₀(t₀x) + s₁(t₁x) = x`: `sum_range` read on the left of `x`.  The
right-module mirror of `LeavittFamily.mul_s_mul_t` in `LeavittModuleRank.lean`. -/
theorem s_mul_add_t_mul (x : A) :
    L.s0 * (L.t0 * x) + L.s1 * (L.t1 * x) = x := by
  rw [← mul_assoc, ← mul_assoc, ← add_mul, L.sum_range, one_mul]

/-- `t₀(s₀y+s₁z) = y`: the first component of the right-module inverse
identity. -/
theorem t0_mul_add_s_mul (y z : A) :
    L.t0 * (L.s0 * y + L.s1 * z) = y := by
  rw [mul_add, ← mul_assoc, ← mul_assoc, L.t0_s0, L.t0_s1, one_mul, zero_mul,
    add_zero]

/-- `t₁(s₀y+s₁z) = z`: the second component of the right-module inverse
identity. -/
theorem t1_mul_add_s_mul (y z : A) :
    L.t1 * (L.s0 * y + L.s1 * z) = z := by
  rw [mul_add, ← mul_assoc, ← mul_assoc, L.t1_s0, L.t1_s1, zero_mul, one_mul,
    zero_add]

/-- **The printed right-module isomorphism of the binary example**
(`non_mf_groups_exist.tex`, "the binary example", equation `eq:leavitt`):
`x ↦ (t₀x,t₁x)` and `(y,z) ↦ s₀y+s₁z` are mutually inverse isomorphisms of
right `A`-modules between `A` and `A × A`.  Spelled as a `LinearEquiv` over
`Aᵐᵒᵖ` (`Semiring.toOppositeModule`), Mathlib's convention for a right module
as a left module over the opposite ring. -/
def rightLinearEquivSquare : A ≃ₗ[Aᵐᵒᵖ] A × A where
  toFun x := (L.t0 * x, L.t1 * x)
  map_add' x y := by
    refine Prod.ext ?_ ?_
    · exact mul_add L.t0 x y
    · exact mul_add L.t1 x y
  map_smul' c x := by
    refine Prod.ext ?_ ?_
    · exact (mul_assoc L.t0 x c.unop).symm
    · exact (mul_assoc L.t1 x c.unop).symm
  invFun y := L.s0 * y.1 + L.s1 * y.2
  left_inv x := L.s_mul_add_t_mul x
  right_inv y := by
    refine Prod.ext ?_ ?_
    · exact L.t0_mul_add_s_mul y.1 y.2
    · exact L.t1_mul_add_s_mul y.1 y.2

@[simp] theorem rightLinearEquivSquare_apply (x : A) :
    L.rightLinearEquivSquare x = (L.t0 * x, L.t1 * x) := rfl

@[simp] theorem rightLinearEquivSquare_symm_apply (y : A × A) :
    L.rightLinearEquivSquare.symm y = L.s0 * y.1 + L.s1 * y.2 := rfl

/-! ## Complete prefix codes, and `GLₘ(A) ≅ Aˣ`, at every leaf count `m ≥ 1` -/

/-- **`GLₘ(A) ≅ Aˣ` for every `m ≥ 1`.**  The self-similarity of Proposition
`prop:selfsim` at the `m`-leaf complete left-comb prefix code
`leftCombCode (m - 1)`.  `UnitGroupHeadline.lean`'s `glFourEquivUnits` is the
`m = 4` instance of this. -/
theorem nonempty_prefixUnitsEquiv {m : ℕ} (hm : 1 ≤ m) :
    Nonempty ((Matrix (Fin m) (Fin m) A)ˣ ≃* Aˣ) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact ⟨L.prefixUnitsEquiv (leftCombCode n) (L.leftCombCode_complete n)⟩

end LeavittFamily

/-! ## Specialization to `R = L_{𝔽₂}(1,2)`, the ring of `thm:headline` -/

namespace UniversalLeavitt

/-- **`Rˣ ≅ ELₙ(R)` for every `n ≥ 2`**, at `R = L_{𝔽₂}(1,2)`: the group
isomorphism from `LeavittFamily.nonempty_prefixUnitsEquiv`, transported along
`BinaryLeavitt.elementaryGroup_eq_top` (`GLₙ(R) = ELₙ(R)`).  This is the
Introduction's claim `H ≅ GL_n(R) = EL_n(R)` for every `n ≥ 2`, at every rank
rather than only the `n = 4` used later; `UnitGroupHeadline.lean` proves the
same fact at `n = 4` together with the rest of `thm:headline`. -/
theorem nonempty_unitsMulEquiv_elementaryGroup {n : ℕ} (hn : 2 ≤ n) :
    Nonempty ((BinaryLeavittAlgebra)ˣ ≃*
      elementaryGroup (Fin n) BinaryLeavittAlgebra) := by
  have htop : elementaryGroup (Fin n) BinaryLeavittAlgebra = ⊤ :=
    BinaryLeavitt.elementaryGroup_eq_top (ZMod 2) n hn
  obtain ⟨e⟩ := family.nonempty_prefixUnitsEquiv (show 1 ≤ n by omega)
  exact ⟨(((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).trans e).symm⟩

/-! ## The two printed sentences, as closed propositions -/

/-- **The Introduction's printed sentence**, `non_mf_groups_exist.tex` line
~155–157: "The right module `R_R` over `R = L_{𝔽₂}(1,2)` ... and `H` is its
automorphism group; Khanh--Thanh show that `H ≅ GL_n(R) = EL_n(R)` for every
`n ≥ 2`", at `R = L_{𝔽₂}(1,2)` (Khanh--Thanh, Proposition 4.2 and Corollary
4.4 — attribution, not a hypothesis: every clause below is a proved theorem).
The `R_R ≅ R_R ⊕ R_R` clause of the same sentence is
`PrintedRightModuleSelfSimilarity` below, at `n = 2`. -/
def PrintedGLElUnitsAllRanks : Prop :=
  Nonempty ((BinaryLeavittAlgebra)ˣ ≃*
      (Module.End (BinaryLeavittAlgebra)ᵐᵒᵖ BinaryLeavittAlgebra)ˣ) ∧
    ∀ n : ℕ, 2 ≤ n →
      Nonempty ((BinaryLeavittAlgebra)ˣ ≃* elementaryGroup (Fin n) BinaryLeavittAlgebra)

theorem manuscriptSentence_glElUnitsAllRanks : PrintedGLElUnitsAllRanks :=
  ⟨⟨unitsEquivEndUnits BinaryLeavittAlgebra⟩,
    fun _ hn => nonempty_unitsMulEquiv_elementaryGroup hn⟩

/-- **The binary example's printed sentence**, `non_mf_groups_exist.tex`
line ~1117–1119: "the maps `x ↦ (t₀x,t₁x)` and `(y,z) ↦ s₀y+s₁z` are mutually
inverse isomorphisms of right `R`-modules between `R` and `R ⊕ R`", at
`R = L_{𝔽₂}(1,2)`.  The existential pins the exact printed formulas on top of
the bundled `LinearEquiv`, which already carries additivity, right-`R`-linearity,
and that the two maps are mutually inverse. -/
def PrintedRightModuleSelfSimilarity : Prop :=
  ∃ e : (BinaryLeavittAlgebra) ≃ₗ[(BinaryLeavittAlgebra)ᵐᵒᵖ]
      BinaryLeavittAlgebra × BinaryLeavittAlgebra,
    (∀ x, e x = (family.t0 * x, family.t1 * x)) ∧
      (∀ y z, e.symm (y, z) = family.s0 * y + family.s1 * z)

theorem manuscriptSentence_rightModuleSelfSimilarity :
    PrintedRightModuleSelfSimilarity :=
  ⟨family.rightLinearEquivSquare, fun _ => rfl, fun _ _ => rfl⟩

end UniversalLeavitt

end GroupApproximation

/-! ## Audit -/

#audit_closed_axioms GroupApproximation.UniversalLeavitt.manuscriptSentence_glElUnitsAllRanks
#audit_closed_axioms GroupApproximation.UniversalLeavitt.manuscriptSentence_rightModuleSelfSimilarity
