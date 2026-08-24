import GroupApproximation.Leavitt.LeavittRankEquivalence
import GroupApproximation.Leavitt.UniversalLeavitt
import GroupApproximation.PropertyT.FiniteFieldElementaryPropertyT

/-!
# Property `(T)` for the rank-twelve binary Leavitt group

Fix `R = L_{𝔽₂}(1,2)`, the universal binary Leavitt algebra over `ZMod 2`.
This module records Kazhdan's property `(T)` for the three elementary groups
the rank-twelve development actually uses:

* `EL₃(R)` — the manuscript's upper-left corner `L`;
* `EL₁₂(R)` — the manuscript's headline group `H`;
* `EL_{(Fin 2 × Fin 2) × Fin 3}(R)` — the same group carried on the nested
  index type in which `Leavitt.RankTwelveCompressor` writes the block
  matrices `X`, `Y` and the compressor `τ = diag(X, Y)`.

The bridge between the last two is the explicit flattening
`((a, b), c) ↦ 6a + 3b + c` of `frame`, transported through
`elementaryReindexEquiv`.

## Literature status

`non_mf_groups_exist.tex` writes, in the proof of `thm:headline` and again in
the paragraph introducing `H = EL₁₂(R)` and `L = EL₃(R)`, that "Both groups
have property~(T) by the theorem of Ershov and Jaikin-Zapirain".  That is a
**citation** in the printed text.  This repository does not depend on it: the
rank-three case over an arbitrary finite coefficient field is proved outright
in `PropertyT.FiniteFieldElementaryPropertyT`, as
`finiteFieldElementaryThree_hasKazhdanPropertyT`, from the in-repo two-root
moving-mass estimate together with the free-algebra presentation of a
finite-type algebra.  Rank twelve is then reached from rank three by the
explicit complete left-comb Leavitt equivalences of
`Leavitt.LeavittRankEquivalence`, which are also proved in this repository.
Every statement below therefore carries **no literature dependence**; the
citation in the manuscript is an attribution of priority, not an assumed
input.
-/

namespace GroupApproximation
namespace RankTwelve

/-- The manuscript's coefficient ring `R = L_{𝔽₂}(1,2)`. -/
noncomputable abbrev Coeff := UniversalLeavitt.BinaryLeavittAlgebra

/-! ## Property `(T)` in rank three and rank twelve -/

/-- **The manuscript's corner `L = EL₃(R)` has property `(T)`.**  This is the
in-repo finite-field rank-three theorem applied to `k = 𝔽₂` and `A = R`; the
Leavitt algebra is a finite-type `𝔽₂`-algebra because it is a quotient of the
free algebra on the four generators `s₀, s₁, t₀, t₁`. -/
theorem corner_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin 3) Coeff) :=
  finiteFieldElementaryThree_hasKazhdanPropertyT (k := ZMod 2) (A := Coeff)

/-- **The manuscript's headline group `H = EL₁₂(R)` has property `(T)`.**
All positive elementary ranks over a binary Leavitt ring are isomorphic, by
the complete left-comb prefix code, so rank twelve inherits rank three. -/
theorem hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin 12) Coeff) :=
  (UniversalLeavitt.family).rankSucc_propertyT_of_rankSucc 11 2 (by omega)
    (by omega) corner_hasKazhdanPropertyT

/-! ## The nested rank-twelve index type -/

/-- The manuscript's block ordering `((a, b), c) ↦ 6a + 3b + c`, flattening the
nested index type used by `Leavitt.RankTwelveCompressor` — outer `Fin 2` for
the `diag(X, Y)` split, middle `Fin 2` for the two `3 × 3` blocks of each
`6 × 6` half, inner `Fin 3` for the Kazhdan corner — onto `Fin 12`. -/
def frame : (Fin 2 × Fin 2) × Fin 3 ≃ Fin 12 where
  toFun x := ⟨6 * x.1.1.val + 3 * x.1.2.val + x.2.val, by
    have h1 := x.1.1.isLt
    have h2 := x.1.2.isLt
    have h3 := x.2.isLt
    omega⟩
  invFun n := ((⟨n.val / 6, by have := n.isLt; omega⟩,
      ⟨n.val / 3 % 2, by omega⟩), ⟨n.val % 3, by omega⟩)
  left_inv := by
    rintro ⟨⟨a, b⟩, c⟩
    refine Prod.ext (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) (Fin.ext ?_)
    · have hb := b.isLt
      have hc := c.isLt
      show (6 * a.val + 3 * b.val + c.val) / 6 = a.val
      omega
    · have hb := b.isLt
      have hc := c.isLt
      show (6 * a.val + 3 * b.val + c.val) / 3 % 2 = b.val
      omega
    · have hc := c.isLt
      show (6 * a.val + 3 * b.val + c.val) % 3 = c.val
      omega
  right_inv := by
    intro n
    refine Fin.ext ?_
    show 6 * (n.val / 6) + 3 * (n.val / 3 % 2) + n.val % 3 = n.val
    omega

/-- `frame` is the printed index formula `6a + 3b + c`. -/
theorem frame_val (x : (Fin 2 × Fin 2) × Fin 3) :
    (frame x).val = 6 * x.1.1.val + 3 * x.1.2.val + x.2.val := rfl

/-- The reindexing isomorphism between the nested and flat rank-twelve
elementary groups. -/
noncomputable def frameEquiv :
    elementaryGroup ((Fin 2 × Fin 2) × Fin 3) Coeff ≃*
      elementaryGroup (Fin 12) Coeff :=
  elementaryReindexEquiv (R := Coeff) frame

/-- **Property `(T)` on the nested rank-twelve index type.**  This is the form
in which the block calculations of `Leavitt.RankTwelveCompressor` present the
twelve coordinates. -/
theorem nested_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0}
      (elementaryGroup ((Fin 2 × Fin 2) × Fin 3) Coeff) :=
  HasKazhdanPropertyT.of_mulEquiv frameEquiv hasKazhdanPropertyT

/-! ## Countability and infinitude -/

private noncomputable def entries (g : elementaryGroup (Fin 12) Coeff) :
    Fin 12 → Fin 12 → Coeff :=
  fun i j ↦
    (↑(g : (Matrix (Fin 12) (Fin 12) Coeff)ˣ) :
      Matrix (Fin 12) (Fin 12) Coeff) i j

private theorem entries_injective : Function.Injective entries := by
  intro x y h
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact congrFun (congrFun h i) j

/-- The headline group is countable: `R` is countable, so a `12 × 12` matrix
over `R` is determined by countably many entries. -/
theorem countable : Countable (elementaryGroup (Fin 12) Coeff) := by
  haveI : Countable (ZMod 2) := Finite.to_countable
  exact entries_injective.countable

/-- The nested-index form of the headline group is countable as well. -/
theorem nested_countable :
    Countable (elementaryGroup ((Fin 2 × Fin 2) × Fin 3) Coeff) := by
  haveI : Countable (elementaryGroup (Fin 12) Coeff) := countable
  exact Countable.of_equiv _ frameEquiv.symm.toEquiv

/-- The headline group is infinite: `R` is infinite, and the elementary root
`e₀₁` embeds it. -/
theorem infinite : Infinite (elementaryGroup (Fin 12) Coeff) :=
  elementaryGroup_infinite (R := Coeff) (0 : Fin 12) 1 (by decide)

/-- The nested-index form of the headline group is infinite as well. -/
theorem nested_infinite :
    Infinite (elementaryGroup ((Fin 2 × Fin 2) × Fin 3) Coeff) :=
  elementaryGroup_infinite (R := Coeff)
    (((0, 0), 0) : (Fin 2 × Fin 2) × Fin 3)
    (((0, 0), 1) : (Fin 2 × Fin 2) × Fin 3) (by decide)

/-- The structural profile of the rank-twelve group established here, with no
literature dependence. -/
theorem profile :
    HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin 12) Coeff) ∧
      Countable (elementaryGroup (Fin 12) Coeff) ∧
      Infinite (elementaryGroup (Fin 12) Coeff) :=
  ⟨hasKazhdanPropertyT, countable, infinite⟩

end RankTwelve
end GroupApproximation
