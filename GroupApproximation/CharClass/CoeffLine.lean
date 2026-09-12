import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Lines over a field: the replacement for "`F₂` has one nonzero element"

Five places in the mod-2 `CharClass` tree identify two nonzero classes of a
one-dimensional group by the brute fact that `F₂ ∖ {0} = {1}`:

* `ProjectiveSpaceCohomology.lean` l.56 and `ProjectiveSpaceRing.lean` l.58-59 —
  `∀ z : ZMod 2, z = 0 ∨ z = 1`;
* `RelativeLineHomotopy.lean` l.72 — `∀ x y : ZMod 2, x ≠ 0 → y ≠ 0 → x = y`;
* `ThomStepCEuler.lean` l.59 and `CohomologyKunnethInjective.lean` l.65 —
  `∀ c : ZMod 2, c ≠ 0 → c = 1`.

Over any field the correct statement is not "equal to the generator" but "a
**unit** multiple of the generator", and that is enough everywhere those five
sites are used, because they are all used to prove that something is nonzero.
This file provides that statement once.

`LemmaTwoStepCEuler.lean`'s module docstring already flags the mod-2 shortcut as
"special to mod-2 coefficients"; this is what replaces it.

## Main declarations

* `Line K M` — `M` is a `K`-line, i.e. `M ≃ₗ[K] K`.
* `exists_smul_of_line` — every element of a line is a scalar multiple of any
  nonzero element.
* `exists_ne_zero_smul_of_line` — and the scalar is nonzero when the element is.
* `eq_of_line_of_ne_zero_zmod2` — at `K = ZMod 2` the scalar is `1`, recovering
  the mod-2 statement verbatim.
-/

namespace GroupApproximation.CharClass

/-- `M` is a **line** over `K`: a `K`-module linearly isomorphic to `K`.  This is
the shape the mod-2 tree already uses (`Hmod2 X n ≃ₗ[ZMod 2] ZMod 2`), stated for
a general coefficient field. -/
abbrev Line (K M : Type) [Field K] [AddCommGroup M] [Module K M] := M ≃ₗ[K] K

variable {K M : Type} [Field K] [AddCommGroup M] [Module K M]

/-- A linear isomorphism onto `K` sends a nonzero element to a nonzero scalar. -/
theorem line_apply_ne_zero (e : Line K M) {x : M} (hx : x ≠ 0) : e x ≠ 0 := by
  intro h
  exact hx (by simpa using congrArg e.symm h)

/-- **Every element of a line is a scalar multiple of any nonzero element.**  This
is the statement that replaces `∀ z : ZMod 2, z = 0 ∨ z = 1`. -/
theorem exists_smul_of_line (e : Line K M) {x : M} (hx : x ≠ 0) (a : M) :
    ∃ c : K, a = c • x := by
  refine ⟨e a / e x, ?_⟩
  apply e.injective
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ (line_apply_ne_zero e hx)]

/-- **A nonzero element of a line is a nonzero multiple of any nonzero element.**
This is the statement that replaces `∀ x y : ZMod 2, x ≠ 0 → y ≠ 0 → x = y`. -/
theorem exists_ne_zero_smul_of_line (e : Line K M) {x : M} (hx : x ≠ 0) {a : M}
    (ha : a ≠ 0) : ∃ c : K, c ≠ 0 ∧ a = c • x := by
  obtain ⟨c, hc⟩ := exists_smul_of_line e hx a
  refine ⟨c, ?_, hc⟩
  rintro rfl
  exact ha (by rw [hc, zero_smul])

/-- A nonzero multiple of a nonzero element of a line is nonzero. -/
theorem smul_ne_zero_of_line (e : Line K M) {x : M} (hx : x ≠ 0) {c : K} (hc : c ≠ 0) :
    c • x ≠ 0 := by
  intro h
  apply line_apply_ne_zero e hx
  have : c * e x = 0 := by simpa using congrArg e h
  exact (mul_eq_zero.1 this).resolve_left hc

/-- **A generator of a line**: the preimage of `1`.  Over `F₂` this is *the*
nonzero element (`ProjectiveSpaceRing.lineGen`); over a general field it is one
of many, and the lemmas below say only that every nonzero element is a nonzero
multiple of it, which is all the mod-2 tree ever uses it for. -/
def lineGen (e : Line K M) : M := e.symm 1

theorem lineGen_ne_zero (e : Line K M) : lineGen e ≠ 0 := by
  intro h
  have h1 : e (lineGen e) = 0 := by rw [h, map_zero]
  rw [lineGen, LinearEquiv.apply_symm_apply] at h1
  exact one_ne_zero h1

/-- Every nonzero element of a line is a nonzero multiple of the generator. -/
theorem exists_ne_zero_smul_lineGen (e : Line K M) {a : M} (ha : a ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ a = c • lineGen e :=
  exists_ne_zero_smul_of_line e (lineGen_ne_zero e) ha

/-- **The `F₂` instance.**  Over `ZMod 2` the scalar produced by
`exists_ne_zero_smul_of_line` is `1`, so two nonzero elements of a line are
equal — the statement the mod-2 tree uses. -/
theorem eq_of_line_of_ne_zero_zmod2 {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (e : Line (ZMod 2) N) {x a : N} (hx : x ≠ 0) (ha : a ≠ 0) : a = x := by
  obtain ⟨c, hc0, hc⟩ := exists_ne_zero_smul_of_line e hx ha
  have hone : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
  rw [hc, hone c hc0, one_smul]

end GroupApproximation.CharClass
