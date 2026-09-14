import GroupApproximation.Leavitt.ElementaryGroup
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Data.ZMod.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Simplicity for group actions: the interface

`simple_kazhdan_sofic_group.tex` at 37551fd93, `thm:general` and subsection "Simplicity" (l.151–210).
A finitely generated group `Λ` acts minimally and topologically freely on a Cantor set `Z`, and
`R = LC(Z, F_2) ⋊ Λ`:

> Fix such $h$ and $V$, and put $d=3|B_w|$. For $a,b\in B_w$ put $\epsilon_{ab}=e_{aV}u_{ab^{-1}}$.
> … so $k-I_3=(ghg^{-1}-h)h$ and $k^{-1}-I_3=h(ghg^{-1}-h)$ lie in $M_3(A_V)$.

The second half of the printed proof (the matrix units `ε_ab`, the copy `H_V` of `GL_d(F_2)`, the ideal
`J` and `K = G`) uses only the following from `R`:

* a unital ring hom `coeff : LC(Z, F_2) →+* R` that is injective;
* units `u : Λ →* Rˣ` with `u_ξ e_U = e_{ξU} u_ξ` for clopen `U` (printed `u_ξ e_U u_ξ^{-1} = e_{ξU}`).

`IsCovariantPair coeff u` records these. The crossed product `LC(Z, F_2) ⋊ Λ` (sk-lef-action) is one
such pair, and so is `ClopenCrossedProduct T (ZMod 2)` with `Λ = ℤ`.

* `isClopen_smul`: `ξ • U` is clopen;
* `epsilon coeff u hV a b = e_{aV} u_{ab⁻¹}` (printed `ε_ab`);
* `epsilonSpan coeff u B hV`: the additive span of the `ε_ab`, `a, b ∈ B` (printed `A_V`; over `F_2` the
  additive span is the linear span);
* `TranslatesDisjoint B V`: the translates `aV`, `a ∈ B`, are pairwise disjoint. This follows from the
  printed smallness `V ∩ ξV = ∅` for `ξ ∈ B_{2w} ∖ {e}` with `B = B_w`;
* `GeneralCommutatorWitness coeff u n`: every nontrivial normal subgroup `K` of `EL_n(R)` contains
  `k ≠ 1`, with a nonempty clopen `V` and a finite `B ∋ e` whose translates of `V` are pairwise disjoint,
  such that every entry of `k - I` and of `k⁻¹ - I` lies in `epsilonSpan coeff u B hV`.

The first half of the proof (small sets, the noncommuting root `h = e_ij(e_V)`, the products
`fu_a e_V f'u_b ∈ {0, ε_{a,b⁻¹}}`) produces the witness. The second half derives `K = G` from it.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open Pointwise

variable {Λ Z R : Type*} [Group Λ] [TopologicalSpace Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z]
  [Ring R]

/-- `ξ • U` is clopen when `U` is. -/
theorem isClopen_smul (ξ : Λ) {U : Set Z} (hU : IsClopen U) : IsClopen (ξ • U) :=
  ⟨hU.isClosed.smul ξ, hU.isOpen.smul ξ⟩

variable (coeff : LocallyConstant Z (ZMod 2) →+* R) (u : Λ →* Rˣ)

/-- **A covariant pair**: an injective coefficient embedding `LC(Z, F_2) → R` and units `u_ξ` with
`u_ξ e_U = e_{ξU} u_ξ`. -/
structure IsCovariantPair : Prop where
  injective : Function.Injective coeff
  covariance : ∀ (ξ : Λ) {U : Set Z} (hU : IsClopen U),
    (u ξ : R) * coeff (LocallyConstant.charFn (ZMod 2) hU) =
      coeff (LocallyConstant.charFn (ZMod 2) (isClopen_smul ξ hU)) * (u ξ : R)

/-- The printed `ε_ab = e_{aV} u_{ab⁻¹}`. -/
noncomputable def epsilon {V : Set Z} (hV : IsClopen V) (a b : Λ) : R :=
  coeff (LocallyConstant.charFn (ZMod 2) (isClopen_smul a hV)) * (u (a * b⁻¹) : R)

/-- The additive span of the `ε_ab`, `a, b ∈ B` (printed `A_V`). -/
def epsilonSpan (B : Finset Λ) {V : Set Z} (hV : IsClopen V) : AddSubgroup R :=
  AddSubgroup.closure {x | ∃ a ∈ B, ∃ b ∈ B, x = epsilon coeff u hV a b}

/-- The translates `aV`, `a ∈ B`, are pairwise disjoint. -/
def TranslatesDisjoint (B : Finset Λ) (V : Set Z) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, a ≠ b → Disjoint (a • V) (b • V)

/-- **The commutator witness of the printed simplicity proof, for group actions.**  Every nontrivial
normal subgroup of `EL_n(R)` contains `k ≠ 1` whose deviations `k - I` and `k⁻¹ - I` have entries in
the span of the `ε_ab`, `a, b ∈ B`. Here `V` is nonempty and clopen, `e ∈ B`, and the translates `aV`,
`a ∈ B`, are pairwise disjoint. -/
def GeneralCommutatorWitness (n : ℕ) : Prop :=
  ∀ K : Subgroup (elementaryGroup (Fin n) R), K.Normal → K ≠ ⊥ →
    ∃ (V : Set Z) (hV : IsClopen V) (B : Finset Λ) (g : elementaryGroup (Fin n) R),
      V.Nonempty ∧ (1 : Λ) ∈ B ∧ TranslatesDisjoint B V ∧ g ∈ K ∧ g ≠ 1 ∧
      ∀ p q : Fin n,
        (((g : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) - 1) p q ∈
          epsilonSpan coeff u B hV ∧
        ((((g⁻¹ : elementaryGroup (Fin n) R) : (Matrix (Fin n) (Fin n) R)ˣ) :
            Matrix (Fin n) (Fin n) R) - 1) p q ∈ epsilonSpan coeff u B hV

end SimpleKazhdanSofic
end GroupApproximation
