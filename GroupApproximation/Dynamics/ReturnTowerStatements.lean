import Mathlib.Topology.Connected.TotallyDisconnected
import GroupApproximation.Algebra.ReturnTowerUnits
import GroupApproximation.Dynamics.ClopenCrossedProduct

/-!
# Return sections and return towers: interface statements

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`), tex 1708–1731:

> Use $r=2$ for the matrix groups and $r=3$ for the unit group.
> Choose a finite clopen cover $U_1,\dots,U_m$ with
> $U_i\cap T^jU_i=\varnothing$ for $0<|j|<r$.  Starting with $C_0=\varnothing$,
> put $C_i=C_{i-1}\cup\left(U_i\setminus\bigcup_{|j|<r}T^jC_{i-1}\right)$.
> Then $C=C_m$ is clopen, separated from its first $r-1$ translates,
> and $X=\bigcup_{|j|<r}T^jC$.  Its return gaps lie in $[r,2r-1]$:
> a larger gap would have a middle point at distance at least $r$
> from every return.  For $r=1$ simply take $C=X$.
>
> Let $C_h$ be the clopen first-return-time cells and $S_C$ the
> first-return homeomorphism.  Put $p_C=1_C$ and $P_C=p_CR_Xp_C$.
> The unit $v=\sum_h u^h1_{C_h}$ implements $S_C$, and
> $P_C=\operatorname{LC}(C,k)\rtimes_{S_C}\mathbb Z$: split any
> partial shift with endpoints in $C$ according to its successive
> returns.  This is a finite splitting for each fixed shift exponent.
> For $0\le i<2r-1$ put $D_i=\bigcup_{h>i}C_h$, $a_i=u^i1_{D_i}$, $b_i=1_{D_i}u^{-i}$.
> The tower partition gives $b_i a_j=0$ for $i\ne j$,
> $b_i a_i=1_{D_i}$ and $\sum_i a_i b_i=1$.

This module fixes the names that the rest of `cor:dynamic-rank-budget` consumes, ahead of their
proofs:

* `NoShortPeriods T r`: `T^j x ≠ x` for `0 < j < r` (printed: no fixed points for `r = 2`, no
  points of periods one or two for `r = 3`);
* `IsReturnSection T r C`: `C` clopen, separated from its first `r - 1` translates, and
  `X = ⋃_{|j|<r} T^j C`;
* `ReturnGapsIn T C lo hi`: every point of `C` returns to `C` for the first time after `h` steps,
  `lo ≤ h ≤ hi`;
* `returnTime T C x`: the first return time;
* `ReturnSectionStatement`: the section construction (tex 1709–1719);
* `FirstReturnStatement`: return times, clopen cells `C_h`, and the first-return homeomorphism
  `S_C` (tex 1721–1722);
* `ReturnTowerUnitsStatement`: the tower `D_i, a_i, b_i` in `R_X` is a `ReturnTowerUnits` system
  (tex 1727–1731), so `Algebra/ReturnTowerUnits` gives the corner `R_X ≅ E M_{2r-1}(P_C) E`, the
  injection `Φ`, unitization, and elementary flattening;
* `ReturnRingCrossedProductStatement`: `P_C ≅ LC(C,k) ⋊_{S_C} ℤ`, sending coefficients to their
  extensions by zero and the implementing unit to `v = ∑_h u^h 1_{C_h}` (tex 1723–1726).

The topological hypotheses of the printed corollary (compact metrizable zero-dimensional `X`) are
used only by `ReturnSectionStatement`, as compact, Hausdorff and totally disconnected.
-/

namespace GroupApproximation.ChainCore

open MFQuotientUnits

section Defs

variable {X : Type*} [TopologicalSpace X]

/-- `T` has no points of period less than `r`: `T^j x ≠ x` for `0 < j < r`. -/
def NoShortPeriods (T : X ≃ₜ X) (r : ℕ) : Prop :=
  ∀ (x : X) (j : ℕ), 0 < j → j < r → (T ^ (j : ℤ)) x ≠ x

/-- **A return section** (tex 1716–1717): `C` is clopen, separated from its first `r - 1`
translates, and `X = ⋃_{|j|<r} T^j C`. -/
structure IsReturnSection (T : X ≃ₜ X) (r : ℕ) (C : Set X) : Prop where
  isClopen : IsClopen C
  disjoint_image : ∀ j : ℕ, 0 < j → j < r → Disjoint C ((T ^ (j : ℤ)) '' C)
  exists_mem_image : ∀ x : X, ∃ j : ℤ, |j| < r ∧ x ∈ (T ^ j) '' C

/-- **Return gaps in `[lo, hi]`** (tex 1717): every point of `C` first returns to `C` after `h`
steps, with `lo ≤ h ≤ hi`. -/
def ReturnGapsIn (T : X ≃ₜ X) (C : Set X) (lo hi : ℕ) : Prop :=
  ∀ x ∈ C, ∃ h : ℕ, lo ≤ h ∧ h ≤ hi ∧ (T ^ (h : ℤ)) x ∈ C ∧
    ∀ j : ℕ, 0 < j → j < h → (T ^ (j : ℤ)) x ∉ C

open Classical in
/-- The first return time of `x` to `C` (`0` if `x` never returns). -/
noncomputable def returnTime (T : X ≃ₜ X) (C : Set X) (x : X) : ℕ :=
  if h : ∃ n : ℕ, 0 < n ∧ (T ^ (n : ℤ)) x ∈ C then Nat.find h else 0

end Defs

/-- **The section construction** (tex 1709–1719): if `T` has no points of period less than
`r ≥ 1`, then `X` has a return section of spread `r` whose return gaps lie in `[r, 2r - 1]`. -/
def ReturnSectionStatement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    (T : X ≃ₜ X) (r : ℕ), 1 ≤ r → NoShortPeriods T r →
      ∃ C : Set X, IsReturnSection T r C ∧ ReturnGapsIn T C r (2 * r - 1)

/-- **First return** (tex 1721–1722): on a return section, the first return time lies in
`[r, 2r - 1]`, the cells `C_h` are clopen, and the first-return map is a homeomorphism of `C`. -/
def FirstReturnStatement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (T : X ≃ₜ X) (r : ℕ) (C : Set X), 1 ≤ r →
    IsReturnSection T r C →
      (∀ x ∈ C, r ≤ returnTime T C x ∧ returnTime T C x ≤ 2 * r - 1 ∧
        (T ^ (returnTime T C x : ℤ)) x ∈ C) ∧
      (∀ h : ℕ, IsClopen {x | x ∈ C ∧ returnTime T C x = h}) ∧
      ∃ S : C ≃ₜ C, ∀ x : C, (S x : X) = (T ^ (returnTime T C (x : X) : ℤ)) x

/-- **The return tower** (tex 1727–1731): `D_i = {x ∈ C | i < returnTime x}` is clopen, and
`a_i = u^i 1_{D_i}`, `b_i = 1_{D_i} u^{-i}` (`i < 2r - 1`) form a `ReturnTowerUnits` system of
height `2r - 1` and full base rank `r` over `p_C = 1_C`. -/
def ReturnTowerUnitsStatement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (T : X ≃ₜ X) (k : Type) [Ring k] (r : ℕ) (C : Set X)
    (hC : IsReturnSection T r C), 1 ≤ r →
      ∃ τ : ReturnTowerUnits (ClopenCrossedProduct T k) (2 * r - 1) r,
        τ.p = ClopenCrossedProduct.coeff T k (LocallyConstant.charFn k hC.isClopen) ∧
        ∀ i : Fin (2 * r - 1), ∃ hD : IsClopen {x | x ∈ C ∧ (i : ℕ) < returnTime T C x},
          τ.a i = ((ClopenCrossedProduct.unit T k ^ ((i : ℕ) : ℤ) :
              (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) *
            ClopenCrossedProduct.coeff T k (LocallyConstant.charFn k hD) ∧
          τ.b i = ClopenCrossedProduct.coeff T k (LocallyConstant.charFn k hD) *
            ((ClopenCrossedProduct.unit T k ^ (-((i : ℕ) : ℤ)) :
              (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k)

/-- **The return ring** (tex 1723–1726): `P_C = p_C R_X p_C ≅ LC(C, k) ⋊_{S_C} ℤ`, where `S_C` is
the first-return homeomorphism, coefficients go to their extensions by zero, and the implementing
unit goes to `v = ∑_h u^h 1_{C_h}`. -/
def ReturnRingCrossedProductStatement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (T : X ≃ₜ X) (k : Type) [Ring k] (r : ℕ) (C : Set X)
    (hC : IsReturnSection T r C), 1 ≤ r →
      ∃ (S : C ≃ₜ C)
        (hp : IsIdempotentElem
          (ClopenCrossedProduct.coeff T k (LocallyConstant.charFn k hC.isClopen)))
        (θ : ClopenCrossedProduct S k ≃+*
          Corner (ClopenCrossedProduct T k)
            (ClopenCrossedProduct.coeff T k (LocallyConstant.charFn k hC.isClopen)) hp),
        (∀ x : C, (S x : X) = (T ^ (returnTime T C (x : X) : ℤ)) x) ∧
        (∀ (f : LocallyConstant C k) (g : LocallyConstant X k),
          (∀ x : C, g x = f x) → (∀ x : X, x ∉ C → g x = 0) →
            ((θ (ClopenCrossedProduct.coeff S k f) : ClopenCrossedProduct T k)) =
              ClopenCrossedProduct.coeff T k g) ∧
        ∃ v : ℕ → LocallyConstant X k,
          (∀ (h : ℕ) (x : X), v h x = Set.indicator {y | y ∈ C ∧ returnTime T C y = h} 1 x) ∧
          ((θ ((ClopenCrossedProduct.unit S k : (ClopenCrossedProduct S k)ˣ) :
              ClopenCrossedProduct S k) : ClopenCrossedProduct T k)) =
            ∑ h ∈ Finset.range (2 * r),
              ((ClopenCrossedProduct.unit T k ^ (h : ℤ) : (ClopenCrossedProduct T k)ˣ) :
                ClopenCrossedProduct T k) * ClopenCrossedProduct.coeff T k (v h)

end GroupApproximation.ChainCore
