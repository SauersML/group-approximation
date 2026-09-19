import GroupApproximation.CharClass.SteenrodDiagonalTarget
import GroupApproximation.CharClass.CartanGroupRing

/-!
# Steenrod's diagonal into the target with the geometric swap action

The published `Phi` of `SteenrodDiagonalLambda.lean` lands in the **free**
`Λ`-module on pairs, and the chain-map condition is *false* there.  The reason is
worth stating once, because it is the whole equivariant content of the
comparison.

The source `W ⊗ S(X)` is free over `Λ = F₂[ℤ/2]`, because `W` is free and the
action on `S(X)` is trivial.  Its differential's first half is multiplication by
`1 + t`.  So the chain-map condition demands `t • y = T y`, where `T` is the
**geometric factor swap**, which moves the index of a pair.  In the free
`Λ`-module the generator moves *coefficients* instead, and comparing the
coefficient at a pair with the coefficient at its swap separates the two outright.

The target `S(X) ⊗ S(X)` with the swap is simply not free over `Λ`: forcing it to
be free replaces it by `Λ ⊗ S(X) ⊗ S(X)`, on which the generator acts by scalars
and the geometric swap has been discarded.

So the target is the `F₂`-module on pairs with `Λ` acting *through* the swap.
`Λ`-linearly extending from the source basis is legitimate into any `Λ`-module
precisely because the source is free, so nothing about `phiBasis`, `steenrodDiag`
or the boundary identity changes; only the module structure downstream does.

Per the fleet rule on frozen signatures the published `Phi` is kept; the
corrected map is `PhiSwap`.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-! ## 1. The swap on pairs -/

/-- The geometric factor swap on a pair index: exchange the two degrees and the
two simplices.  The degree constraint is re-derived, and since it is a `Prop`
nothing is transported. -/
def swapIdx {X : TopCat.{0}} {k : ℕ} (q : PairIdx X k) : PairIdx X k :=
  ⟨⟨(q.1.val.2, q.1.val.1), by have h := q.1.property; omega⟩, (q.2.2, q.2.1)⟩

@[simp] theorem swapIdx_swapIdx {X : TopCat.{0}} {k : ℕ} (q : PairIdx X k) :
    swapIdx (swapIdx q) = q := rfl

/-- The swap as an `F₂`-linear involution of the module of pairs. -/
def swapEnd (X : TopCat.{0}) (k : ℕ) : Module.End (ZMod 2) (PairIdx X k →₀ ZMod 2) :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) swapIdx

@[simp] theorem swapEnd_single (X : TopCat.{0}) (k : ℕ) (q : PairIdx X k) (c : ZMod 2) :
    swapEnd X k (Finsupp.single q c) = Finsupp.single (swapIdx q) c := by
  unfold swapEnd
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem swapEnd_sq (X : TopCat.{0}) (k : ℕ) : swapEnd X k * swapEnd X k = 1 := by
  apply Finsupp.lhom_ext'
  intro q
  apply LinearMap.ext_ring
  show swapEnd X k (swapEnd X k (Finsupp.single q (1 : ZMod 2))) = Finsupp.single q 1
  rw [swapEnd_single, swapEnd_single, swapIdx_swapIdx]

/-! ## 2. The target module -/

/-- **The target of `Φ`**: the `F₂`-module on pairs, with `Λ` acting through the
geometric swap.  This is the module structure the chain-map condition needs. -/
noncomputable instance tgtModule (X : TopCat.{0}) (k : ℕ) :
    Module GroupRingZ2 (PairIdx X k →₀ ZMod 2) :=
  moduleOfInvolution (swapEnd X k) (swapEnd_sq X k)

/-- **The generator acts as the swap**, by construction.  This is the equation
that turns `(1 + t) • y = y + T y` into the low terms of the boundary identity. -/
theorem groupRingGen_smul (X : TopCat.{0}) (k : ℕ) (y : PairIdx X k →₀ ZMod 2) :
    (groupRingGen : GroupRingZ2) • y = swapEnd X k y :=
  moduleOfInvolution_smul (swapEnd X k) (swapEnd_sq X k) y

theorem one_add_gen_smul (X : TopCat.{0}) (k : ℕ) (y : PairIdx X k →₀ ZMod 2) :
    ((1 : GroupRingZ2) + groupRingGen) • y = y + swapEnd X k y := by
  rw [add_smul, one_smul, groupRingGen_smul]

/-! ## 3. The corrected diagonal -/

/-- `Φ` on a basis element, valued in the `F₂`-module of pairs.  This is the
published `phiBasis` at `Λ = ZMod 2`, moved along the carrier bridge; the
mathematics is unchanged. -/
def phiPair (X : TopCat.{0}) (k : ℕ) (b : WSIndex X k) : PairIdx X k →₀ ZMod 2 :=
  Finsupp.mapDomain (pairIndexToIdx X k) (phiBasis X (ZMod 2) b)

/-- **Steenrod's diagonal**, `Λ`-linear into the target with the swap action.
The extension from the basis is legitimate into any `Λ`-module because the source
is free over `Λ`. -/
noncomputable def PhiSwap (X : TopCat.{0}) (k : ℕ) :
    (WSIndex X k →₀ GroupRingZ2) →ₗ[GroupRingZ2] (PairIdx X k →₀ ZMod 2) :=
  Finsupp.linearCombination GroupRingZ2 (phiPair X k)

theorem PhiSwap_single (X : TopCat.{0}) (k : ℕ) (b : WSIndex X k) (c : GroupRingZ2) :
    PhiSwap X k (Finsupp.single b c) = c • phiPair X k b := by
  unfold PhiSwap
  simp

theorem PhiSwap_single_one (X : TopCat.{0}) (k : ℕ) (b : WSIndex X k) :
    PhiSwap X k (Finsupp.single b 1) = phiPair X k b := by
  rw [PhiSwap_single, one_smul]

end

end Steenrod
end CharClass
end GroupApproximation
