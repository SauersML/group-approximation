import GroupApproximation.Algebra.GroupTorsionFree
import GroupApproximation.Sofic.KazhdanCliffordConstruction

/-!
# The adjoined involution, over an arbitrary base

`non_mf_groups_exist.tex`, `\begin{remark}[a small-cancellation realization]`
(`\label{rem:ff-realization}`; grep the phrase "has torsion even though", never
a line number, the file being under concurrent edit) closes with

> The group `E(P,α,a)` has torsion even though `P` does not, since the
> construction adjoins the involution `c`.

This is proof-ledger row `KC.23`, whose text is "E(P, α, a) contains
involutions whatever the base".  The remark is printed about
Fournier-Facio's group `P`, but nothing in the sentence is about that group:
the involution is adjoined by the construction of
the Kazhdan--Clifford construction, so the assertion holds over *every* base
satisfying that theorem's hypotheses.  That is what is proved here — the
generality is the content, not a weakening, and no hypothesis about the base
beyond the printed ones is used.

## What is proved

* `lamp_ne_one` — the adjoined root involution `c` is nontrivial in
  `E(Γ,α,a)`.  This is the one step with mathematical content, and it is not
  a presentation fact: `c` could conceivably die in the quotient by the
  relators.  It does not, because `w = ⁅tct⁻¹, a(tct⁻¹)a⁻¹⁆` is a word in
  `c` that becomes trivial the moment `c` does, and `w ≠ 1` is already proved
  in `Sofic/KazhdanCliffordConstruction` from the Clifford realization.
* `orderOf_lamp` — `c` has order exactly `2`, and `orderOf_mark` the same for
  the central sign `w`, so the construction exhibits two named involutions.
* `not_isPowerTorsionFree` / `not_isMulTorsionFree` — `E(Γ,α,a)` has torsion,
  whatever the base.  Both torsion-freeness notions of this development are
  refuted; `IsPowerTorsionFree` is the weaker predicate (`GroupTorsionFree`),
  so refuting it is the stronger statement.
* `lamp_notMem_range_iota` — when the base *is* torsion-free, `c` is not in
  the image of the base.  This is the "even though `P` does not" half: the
  torsion is genuinely adjoined rather than inherited, which is exactly what
  the printed clause "since the construction adjoins the involution `c`"
  asserts and what a reader would otherwise have to take on faith.
* `manuscriptFFRealizationTorsion` — the remark's sentence, with the printed
  hypotheses of the Kazhdan--Clifford construction and torsion-freeness of the base.

Property `(T)` of the base is carried in that last statement because the
remark inherits it from the hypotheses of the Kazhdan--Clifford construction; it is
named `_hT` because none of these statements consume it.  The construction's
own hypotheses that *are* consumed are injectivity of `α` and `a ∉ α(Γ)`,
both only through `mark_ne_one`.
-/

namespace GroupApproximation
namespace InvolutionsAnyBase

open KazhdanCliffordConstruction
open scoped commutatorElement

universe w

/-! ## The marked word dies with the lamp -/

/-- The marked compression word of a *trivial* root letter is trivial: with
`c = 1` both entries of the commutator `⁅tct⁻¹, a(tct⁻¹)a⁻¹⁆` collapse.

This is the only computation in the file, and it is what makes nontriviality
of the marked word transfer to nontriviality of the adjoined involution. -/
theorem markedCompressionWord_one {G : Type*} [Group G] (t a : G) :
    markedCompressionWord t a (1 : G) = 1 := by
  have hd : t * (1 : G) * t⁻¹ = 1 := by
    rw [mul_one, mul_inv_cancel]
  show ⁅t * (1 : G) * t⁻¹, a * (t * (1 : G) * t⁻¹) * a⁻¹⁆ = 1
  rw [hd, mul_one, mul_inv_cancel, commutatorElement_one_left]

/-! ## The adjoined involution is nontrivial -/

/-- **The root involution survives the presentation.**  In `E(Γ,α,a)` the
adjoined letter `c` is not the identity.

The presentation imposes `c² = 1` and commutation with the base, and nothing
prevents a quotient from collapsing `c` outright; what rules that out is the
Clifford realization, through `mark_ne_one`.  The hypotheses are therefore
exactly the ones that theorem needs. -/
theorem lamp_ne_one {Γ : Type} [Group Γ] [Group.IsFinitelyPresented Γ]
    (alpha : Γ →* Γ) (hAlpha : Function.Injective alpha) (a : Γ)
    (ha : a ∉ Set.range alpha) :
    lamp alpha a ≠ 1 := by
  intro hone
  refine mark_ne_one alpha hAlpha a ha ?_
  show markedCompressionWord (stable alpha a) (iota alpha a a)
    (lamp alpha a) = 1
  rw [hone, markedCompressionWord_one]

/-- The adjoined letter has order exactly two. -/
theorem orderOf_lamp {Γ : Type} [Group Γ] [Group.IsFinitelyPresented Γ]
    (alpha : Γ →* Γ) (hAlpha : Function.Injective alpha) (a : Γ)
    (ha : a ∉ Set.range alpha) :
    orderOf (lamp alpha a) = 2 :=
  orderOf_eq_prime (lamp_sq alpha a) (lamp_ne_one alpha hAlpha a ha)

/-- The central sign has order exactly two as well, so the construction
produces two named involutions.  No claim is made that they are distinct. -/
theorem orderOf_mark {Γ : Type} [Group Γ] [Group.IsFinitelyPresented Γ]
    (alpha : Γ →* Γ) (hAlpha : Function.Injective alpha) (a : Γ)
    (ha : a ∉ Set.range alpha) :
    orderOf (mark alpha a) = 2 :=
  orderOf_eq_prime (mark_sq alpha a) (mark_ne_one alpha hAlpha a ha)

/-! ## Torsion, whatever the base -/

/-- **`E(Γ,α,a)` has torsion, over every base.**  A nontrivial element of
order two refutes ordinary torsion-freeness. -/
theorem not_isPowerTorsionFree {Γ : Type} [Group Γ]
    [Group.IsFinitelyPresented Γ]
    (alpha : Γ →* Γ) (hAlpha : Function.Injective alpha) (a : Γ)
    (ha : a ∉ Set.range alpha) :
    ¬ IsPowerTorsionFree (Extension alpha a) := by
  intro htf
  exact lamp_ne_one alpha hAlpha a ha
    (htf (lamp alpha a) 2 (by norm_num) (lamp_sq alpha a))

/-- The same for mathlib's stronger unique-root torsion-freeness, which
implies the ordinary one. -/
theorem not_isMulTorsionFree {Γ : Type} [Group Γ]
    [Group.IsFinitelyPresented Γ]
    (alpha : Γ →* Γ) (hAlpha : Function.Injective alpha) (a : Γ)
    (ha : a ∉ Set.range alpha) :
    ¬ IsMulTorsionFree (Extension alpha a) := by
  intro htf
  haveI : IsMulTorsionFree (Extension alpha a) := htf
  exact not_isPowerTorsionFree alpha hAlpha a ha
    IsPowerTorsionFree.of_isMulTorsionFree

/-! ## The torsion is adjoined, not inherited -/

/-- **Over a torsion-free base the involution is new.**  If `Γ` has no
torsion then `c` lies outside the image of `Γ`, so the torsion of
`E(Γ,α,a)` is created by the construction rather than carried in by the
base.  This is the printed clause "since the construction adjoins the
involution `c`".

The base embeds (`iota_injective`), so an equation `c = ι(g)` would make
`g² = 1` inside `Γ`, hence `g = 1` and `c = 1`, contradicting
`lamp_ne_one`. -/
theorem lamp_notMem_range_iota {Γ : Type} [Group Γ]
    [Group.IsFinitelyPresented Γ]
    (alpha : Γ →* Γ) (hAlpha : Function.Injective alpha) (a : Γ)
    (ha : a ∉ Set.range alpha) (hTF : IsPowerTorsionFree Γ) :
    lamp alpha a ∉ Set.range (iota alpha a) := by
  rintro ⟨g, hg⟩
  have hinj : Function.Injective (iota alpha a) :=
    iota_injective alpha hAlpha a ha
  have hpow : iota alpha a (g ^ 2) = 1 := by
    rw [map_pow, hg]
    exact lamp_sq alpha a
  have hg2 : g ^ 2 = 1 := by
    apply hinj
    rw [hpow, map_one]
  have hg1 : g = 1 := hTF g 2 (by norm_num) hg2
  refine lamp_ne_one alpha hAlpha a ha ?_
  rw [← hg, hg1, map_one]

/-! ## The printed remark -/

/-- **`\label{rem:ff-realization}`, over an arbitrary base.**  Under exactly
the hypotheses of the Kazhdan--Clifford construction together with torsion-freeness
of the base — which is what the remark's `P` supplies — the constructed group
`E(Γ,α,a)` has torsion, the torsion is witnessed by the adjoined letter `c`
of order two, and that letter is not in the image of the base.

Property `(T)` is a hypothesis of the theorem being applied and is therefore
carried here, but no clause consumes it, which is why it is named `_hT`.  The
remark's own base is `P`; nothing below is special to it. -/
theorem manuscriptFFRealizationTorsion {Γ : Type} [Group Γ]
    [Group.IsFinitelyPresented Γ]
    (alpha : Γ →* Γ) (hAlpha : Function.Injective alpha) (a : Γ)
    (_hT : HasKazhdanPropertyTComplex.{0, w} Γ)
    (ha : a ∉ Set.range alpha) (hTF : IsPowerTorsionFree Γ) :
    orderOf (lamp alpha a) = 2 ∧
      lamp alpha a ∉ Set.range (iota alpha a) ∧
      ¬ IsPowerTorsionFree (Extension alpha a) ∧
      ¬ IsMulTorsionFree (Extension alpha a) :=
  ⟨orderOf_lamp alpha hAlpha a ha,
    lamp_notMem_range_iota alpha hAlpha a ha hTF,
    not_isPowerTorsionFree alpha hAlpha a ha,
    not_isMulTorsionFree alpha hAlpha a ha⟩

end InvolutionsAnyBase
end GroupApproximation
