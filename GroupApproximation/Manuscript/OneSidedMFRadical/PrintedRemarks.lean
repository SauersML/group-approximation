import GroupApproximation.Manuscript.MFRadicals.SimpleSofic
import GroupApproximation.Manuscript.OneSidedMFRadical.DefectSaturation
import GroupApproximation.Manuscript.OneSidedMFRadical.FiniteDimensionalCommutant
import GroupApproximation.Sofic.Hyperlinear
import GroupApproximation.Sofic.KazhdanTransportFiniteDimensionalInputs
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# The manuscript's printed remarks and scope claims

`non_mf_groups_exist.tex`: the remark following `thm:commutant`, the scope
paragraph following the Introduction's sterility discussion, and the opening
step of the proof of `prop:mf-residual-calculus`.

These are prose sentences carrying real mathematical content.  Each one below
becomes a named closed `Prop` with all binders inside, so `#audit_closed_axioms`
accepts it.

## What this module supplies, and what was already carried elsewhere

**The remark after `thm:commutant`** --- *"The finite-dimensional hypothesis is
essential here.  On an infinite-dimensional space an injective endomorphism of
the commutant need not be surjective."* --- is `Section 1` below.  The step the
printed proof of `thm:commutant` consumes is: an injective `k`-linear self-map
of the commutant `C = ρ(L)'` is surjective *because `C` is finite-dimensional*.
The remark is the failure of exactly that implication, so the formalization
pairs the implication (`commutant_surjective_of_injective`) with a
counterexample to it in infinite dimension.

The counterexample is built on the shift pair already in the development:
`KazhdanTransportFiniteDimensionalInputs.shiftUp` and `shiftDown` satisfy
`shiftDown * shiftUp = 1` and `shiftUp * shiftDown ≠ 1`.  That file states a
*different* printed sentence --- Question 5's *"the proof uses finite
dimensionality of `M_(d_n)(ℂ)` … twice"* --- and its
`not_dedekindFinite_infiniteDimensionalModel` records the failure of Dedekind
finiteness, i.e. that a *one-sided inverse* need not be two-sided.  The remark
after `thm:commutant` is about an *injective endomorphism of the commutant*,
which is a statement about a linear self-map of `C`, not about one-sided
inverses in an algebra.  `shiftConjugation` below is the map the manuscript's
own next sentence points at: `x ↦ S x T` with `T S = 1`, the infinite-dimensional
analogue of the printed conjugation `x ↦ ρ(u) x ρ(u)⁻¹` in which the compressor
is represented by an operator with a one-sided inverse only.  Nothing about the
shifts is re-proved here.

**The Introduction's three sterility consequences** are already carried, in
full, by `Manuscript/OneSidedMFRadical/DefectSaturation.lean`:

* a faithful finite-dimensional linear representation over any field kills the
  printed defect --- `printedDefect_eq_bot_of_faithful_finiteDimensional`;
* residual finiteness kills it --- `printedDefect_eq_bot_of_isResiduallyFinite`;
* a finite `L` kills it --- `printedDefect_eq_bot_of_finite`;

packaged as the closed `PrintedDefectSterility` /
`manuscriptPrintedDefectSterility`.  Nothing there is duplicated below.  What
that package does *not* expose is the printed amenable case's two intermediate
sentences --- *"then `uLu⁻¹ = L`, so `ucu⁻¹` centralizes `L` for every
`u ∈ Comp_G(L)`"* --- which are proved in that file but appear in no closed
endpoint.  `PrintedAmenableCaseChain` in `Section 2` below is exactly that
packaging and adds no new mathematics.

**The scope paragraph** --- *"The argument is specific to operator-norm
approximation.  It does not prove that `H` is nonsofic or nonhyperlinear"* ---
is `Section 3`.  A claim about what is *not* proved is not itself a theorem, so
what is formalized is the separation the paragraph asserts: the criterion's
conclusion, a full MF radical, is compatible with soficity and with
hyperlinearity.  The witness is Theorem~B's envelope
(`Manuscript.MFRadicals.manuscriptTheoremB`), a countable simple **sofic** group
with `Rad_MF = ⊤`.  Two consequences are added here: it is hyperlinear
(soficity implies hyperlinearity), and its shadow residual `R_(∞→2)` is also
everything, since `Rad_MF ≤ R_(∞→2)`.  So neither a full MF radical nor a full
shadow residual can witness non-soficity or non-hyperlinearity.

**The first step of the proof of `prop:mf-residual-calculus`** --- *"An
intersection of kernels is normal"* --- is `Section 4`.  For the printed object
`cl_MF^G(N)` this is already the instance `literalMFClosure_normal` in
`LiteralMFClosure.lean`; what is missing is the general sentence, which is
supplied here in both the indexed and the set form.  The printed proof's second
step --- *"If `α` is an endomorphism of `G` … `π ∘ α` kills `x` … which proves
full invariance"* --- is already carried verbatim: `map_manuscriptCoronaMFResidual_le`
is proved by `exact hx d hd (rho.comp f)`, which is that sentence, and it is the
`IsFullyInvariant` clause of both `manuscriptMFResidualCalculus` and
`manuscriptMFResidualCalculusLiteral`.  It is not restated below.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open KazhdanTransportFiniteDimensionalInputs

universe u v w

noncomputable section

/-! ## 1. The remark after `thm:commutant`

The printed proof of `thm:commutant` runs: conjugation by `ρ(u)⁻¹` maps
`C = ρ(L)'` into itself, it is injective, and *`C` is finite-dimensional*,
hence the inclusion is an equality.  The remark says the last step is where
finite dimensionality is spent. -/

/-- **The step `thm:commutant` consumes.**  In finite dimension every injective
`k`-linear endomorphism of the commutant `ρ(L)'` --- represented, as everywhere
in this development, as the fixed submodule of the adjoint representation --- is
surjective. -/
theorem commutant_surjective_of_injective {H : Type u} {k : Type v} {W : Type w}
    [Group H] [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (rho : H →* (W ≃ₗ[k] W)) (L : Subgroup H)
    {Phi : ↥(fixedSubmodule (adjointRep rho) L) →ₗ[k]
      ↥(fixedSubmodule (adjointRep rho) L)}
    (hPhi : Function.Injective Phi) : Function.Surjective Phi :=
  LinearMap.injective_iff_surjective.mp hPhi

/-- The commutant of the image of the trivial subgroup is the whole
endomorphism algebra.  This is what makes a statement about `End_k(V)` a
statement about a commutant `ρ(L)'`. -/
theorem fixedSubmodule_bot_eq_top {H : Type u} {k : Type v} {W : Type w}
    [Group H] [Field k] [AddCommGroup W] [Module k W]
    (sigma : H →* (W ≃ₗ[k] W)) :
    fixedSubmodule sigma (⊥ : Subgroup H) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x ↦ ?_
  show ∀ gamma ∈ (⊥ : Subgroup H), sigma gamma x = x
  intro gamma hgamma
  rw [Subgroup.mem_bot] at hgamma
  subst hgamma
  simp

/-- **The infinite-dimensional analogue of the printed conjugation.**
`x ↦ S x T` for the shift pair `S = shiftUp`, `T = shiftDown`, which satisfies
`T S = 1` but not `S T = 1`.  In finite dimension the compressor's image is
invertible and this map is a genuine conjugation; here it is only a one-sided
one, which is precisely the situation the manuscript's next sentence hands to
the norm matrix corona. -/
def shiftConjugation : Module.End ℂ (ℕ → ℂ) →ₗ[ℂ] Module.End ℂ (ℕ → ℂ) :=
  (LinearMap.mulRight ℂ shiftDown).comp (LinearMap.mulLeft ℂ shiftUp)

theorem shiftConjugation_apply (x : Module.End ℂ (ℕ → ℂ)) :
    shiftConjugation x = shiftUp * x * shiftDown := rfl

/-- One-sided conjugation by the shift pair is injective: `shiftDown * shiftUp = 1`
makes `y ↦ T y S` a left inverse of it. -/
theorem shiftConjugation_injective : Function.Injective shiftConjugation := by
  have key : ∀ z : Module.End ℂ (ℕ → ℂ),
      shiftDown * (shiftUp * z * shiftDown) * shiftUp = z := by
    intro z
    have hassoc : shiftDown * (shiftUp * z * shiftDown) * shiftUp
        = shiftDown * shiftUp * (z * (shiftDown * shiftUp)) := by
      calc shiftDown * (shiftUp * z * shiftDown) * shiftUp
        _ = shiftDown * (shiftUp * z * shiftDown * shiftUp) := mul_assoc _ _ _
        _ = shiftDown * (shiftUp * z * (shiftDown * shiftUp)) := by
            rw [mul_assoc (shiftUp * z) shiftDown shiftUp]
        _ = shiftDown * (shiftUp * (z * (shiftDown * shiftUp))) := by
            rw [mul_assoc shiftUp z (shiftDown * shiftUp)]
        _ = shiftDown * shiftUp * (z * (shiftDown * shiftUp)) :=
            (mul_assoc _ _ _).symm
    rw [hassoc, shiftDown_mul_shiftUp, one_mul, mul_one]
  intro x y hxy
  rw [shiftConjugation_apply, shiftConjugation_apply] at hxy
  have hx : shiftDown * (shiftUp * x * shiftDown) * shiftUp = x := key x
  rw [hxy] at hx
  exact hx.symm.trans (key y)

/-- **And it is not surjective.**  Its image lands in the operators killing the
first coordinate, so the identity is not attained. -/
theorem shiftConjugation_not_surjective :
    ¬ Function.Surjective shiftConjugation := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj 1
  rw [shiftConjugation_apply] at hx
  have hv : ((shiftUp * x * shiftDown) (fun n ↦ if n = 0 then (1 : ℂ) else 0)) 0
      = ((1 : Module.End ℂ (ℕ → ℂ)) (fun n ↦ if n = 0 then (1 : ℂ) else 0)) 0 := by
    rw [hx]
  have hleft :
      ((shiftUp * x * shiftDown) (fun n ↦ if n = 0 then (1 : ℂ) else 0)) 0
        = 0 := rfl
  have hright :
      ((1 : Module.End ℂ (ℕ → ℂ)) (fun n ↦ if n = 0 then (1 : ℂ) else 0)) 0
        = 1 := by
    simp
  rw [hleft, hright] at hv
  exact zero_ne_one hv

/-- **The remark after `thm:commutant`, as one closed proposition.**

1. The step the printed proof takes: in finite dimension every injective
   `k`-linear endomorphism of the commutant `ρ(L)'` is surjective.
2. `End_ℂ(ℂ^ℕ)` really is a commutant: it is `ρ(1)'` for every linear
   representation on `ℂ^ℕ`.
3. On that infinite-dimensional commutant the step fails --- there is an
   injective `ℂ`-linear endomorphism which is not surjective.

Together: the finite-dimensional hypothesis is exactly what the step needs, and
it cannot be dropped. -/
def CommutantFiniteDimensionalHypothesisIsEssential : Prop :=
  (∀ (H : Type u) (k : Type v) (W : Type w) [Group H] [Field k]
      [AddCommGroup W] [Module k W] [FiniteDimensional k W]
      (rho : H →* (W ≃ₗ[k] W)) (L : Subgroup H)
      (Phi : ↥(fixedSubmodule (adjointRep rho) L) →ₗ[k]
        ↥(fixedSubmodule (adjointRep rho) L)),
      Function.Injective Phi → Function.Surjective Phi) ∧
    (∀ (H : Type u) [Group H] (rho : H →* ((ℕ → ℂ) ≃ₗ[ℂ] (ℕ → ℂ))),
      fixedSubmodule (adjointRep rho) (⊥ : Subgroup H) = ⊤) ∧
    (∃ Phi : Module.End ℂ (ℕ → ℂ) →ₗ[ℂ] Module.End ℂ (ℕ → ℂ),
      Function.Injective Phi ∧ ¬ Function.Surjective Phi)

/-- Closed proof of the manuscript's remark after `thm:commutant`. -/
theorem manuscriptCommutantFiniteDimensionalHypothesisIsEssential :
    CommutantFiniteDimensionalHypothesisIsEssential := by
  refine ⟨?_, ?_, ?_⟩
  · intro H k W _ _ _ _ _ rho L Phi hPhi
    exact commutant_surjective_of_injective rho L hPhi
  · intro H _ rho
    exact fixedSubmodule_bot_eq_top (adjointRep rho)
  · exact ⟨shiftConjugation, shiftConjugation_injective,
      shiftConjugation_not_surjective⟩

/-! ## 2. The Introduction's amenable case, with its printed intermediate steps

The three sterility consequences themselves are `PrintedDefectSterility` in
`DefectSaturation.lean` and are not restated.  What follows packages the two
sentences the printed amenable case passes through --- `uLu⁻¹ = L`, and
`ucu⁻¹` centralizes `L` --- together with their conclusion.  All three are
proved in `DefectSaturation.lean`; only the packaging is new. -/

/-- **The printed amenable case, in full.**  For a finite `L`: every one-sided
compressor conjugates `L` *onto* `L`; consequently `ucu⁻¹` centralizes `L` for
every `u ∈ Comp_G(L)` and every `c ∈ C_G(L)`; consequently `𝔇_G(L) = 1`.

The analytic input of the printed case --- that an amenable group's
property-`(T)` subgroup is finite --- is the cited `BHV` fact and is *not*
proved here; the hypothesis `Finite ↥L` is where it would enter. -/
def PrintedAmenableCaseChain : Prop :=
  ∀ (G : Type u) [Group G] (L : Subgroup G), Finite ↥L →
    (∀ u ∈ compressionSet L,
        (fun x ↦ u * x * u⁻¹) '' (L : Set G) = (L : Set G)) ∧
      (∀ u ∈ compressionSet L, ∀ c : G, (∀ d ∈ L, Commute c d) →
        ∀ ell ∈ L, Commute (u * c * u⁻¹) ell) ∧
      printedDefect L = ⊥

/-- Closed proof of the printed amenable-case chain. -/
theorem manuscriptPrintedAmenableCaseChain : PrintedAmenableCaseChain := by
  intro G _ L hL
  haveI := hL
  refine ⟨fun u hu ↦ conj_image_eq_of_mem_compressionSet_of_finite hu, ?_,
    printedDefect_eq_bot_of_finite L⟩
  intro u hu c hc ell hell
  exact commute_conj_of_mem_compressionSet_of_finite hu hc hell

/-! ## 3. The scope paragraph

*"The argument is specific to operator-norm approximation.  It does not prove
that `H` is nonsofic or nonhyperlinear: normalized Hilbert--Schmidt
approximations do not provide the operator-norm control used to construct the
conjugation representation in `thm:transport`."*

A claim about what a proof does not establish is not a theorem.  What is a
theorem, and is what the paragraph is protecting, is that the conclusion the
criterion does reach --- a full MF radical, and with it a full shadow residual
`R_(∞→2)` --- is compatible with soficity and with hyperlinearity.  So no route
from that conclusion to non-soficity exists. -/

/-- **A countable sofic group with everything invisible.**  Theorem~B's simple
sofic envelope, with the two consequences the scope paragraph needs: it is
hyperlinear, and its shadow residual `R_(∞→2)` is the whole group.

The residual clause is `Rad_MF ≤ R_(∞→2)` applied to a full radical; no new
analysis is involved. -/
def SoficityIsNotObstructedByFullRadicals : Prop :=
  ∃ (U : Ultrafilter ℕ) (X : ℕ → FiniteModel)
    (E : Subgroup (UniversalSofic U X)),
    Countable ↥E ∧ Nontrivial ↥E ∧ IsSofic ↥E ∧ IsHyperlinear ↥E ∧
      actualCoronaMFResidual ↥E = ⊤ ∧
      manuscriptCoronaMFResidual ↥E = ⊤ ∧
      opToHSShadowResidual ↥E = ⊤ ∧
      ¬ IsOperatorMF ↥E

/-- Closed proof that soficity survives a full MF radical and a full shadow
residual. -/
theorem manuscriptSoficityIsNotObstructedByFullRadicals :
    SoficityIsNotObstructedByFullRadicals := by
  obtain ⟨U, X, E, hcount, hsimple, hsofic, hrad, -, hnot⟩ :=
    MFRadicals.manuscriptTheoremB
  haveI : Countable ↥E := hcount
  refine ⟨U, X, E, hcount, hsimple.toNontrivial, hsofic,
    isHyperlinear_of_isSofic hsofic, hrad, ?_, ?_, hnot⟩
  · rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
    exact hrad
  · refine top_unique ?_
    rw [← hrad]
    exact (manuscriptMFResidualLeShadowResidual ↥E).2

/-- **The scope paragraph's mathematical content.**  Neither a full MF radical
nor a full operator-to-Hilbert--Schmidt shadow residual entails non-soficity,
and neither entails non-hyperlinearity.  Each clause is the negation of a
*universally quantified* implication with a nontriviality guard, so none of them
is discharged by the trivial group. -/
def FullRadicalsDoNotEntailNonsoficity : Prop :=
  (¬ ∀ (G : Type) [Group G] [Countable G] [Nontrivial G],
      actualCoronaMFResidual G = ⊤ → ¬ IsSofic G) ∧
    (¬ ∀ (G : Type) [Group G] [Countable G] [Nontrivial G],
      actualCoronaMFResidual G = ⊤ → ¬ IsHyperlinear G) ∧
    (¬ ∀ (G : Type) [Group G] [Countable G] [Nontrivial G],
      opToHSShadowResidual G = ⊤ → ¬ IsSofic G) ∧
    (¬ ∀ (G : Type) [Group G] [Countable G] [Nontrivial G],
      opToHSShadowResidual G = ⊤ → ¬ IsHyperlinear G)

/-- Closed proof of the scope paragraph's separation. -/
theorem manuscriptFullRadicalsDoNotEntailNonsoficity :
    FullRadicalsDoNotEntailNonsoficity := by
  obtain ⟨_U, _X, E, hcount, hnt, hsofic, hhyp, hrad, -, hshadow, -⟩ :=
    manuscriptSoficityIsNotObstructedByFullRadicals
  haveI : Countable ↥E := hcount
  haveI : Nontrivial ↥E := hnt
  exact ⟨fun h ↦ h ↥E hrad hsofic, fun h ↦ h ↥E hrad hhyp,
    fun h ↦ h ↥E hshadow hsofic, fun h ↦ h ↥E hshadow hhyp⟩

/-! ## 4. The first step of the proof of `prop:mf-residual-calculus`

*"An intersection of kernels is normal."*  For the printed closure
`cl_MF^G(N)`, which is a set-intersection of kernels, this is the instance
`literalMFClosure_normal`.  The general sentence is below, in the indexed and
the set form. -/

/-- An intersection of normal subgroups is normal, in the set form the printed
closure `cl_MF^G(N) = ⋂{ker f : …}` is written with. -/
theorem sInf_normal_of_forall_normal {G : Type u} [Group G]
    (S : Set (Subgroup G)) (hS : ∀ K ∈ S, K.Normal) : (sInf S).Normal := by
  refine ⟨fun x hx g ↦ ?_⟩
  rw [Subgroup.mem_sInf] at hx ⊢
  intro K hK
  exact (hS K hK).conj_mem x (hx K hK) g

/-- **An intersection of kernels is normal**, indexed form. -/
theorem iInf_ker_normal {G : Type u} [Group G] {Idx : Type v}
    {M : Idx → Type w} [∀ i, Group (M i)] (f : ∀ i, G →* M i) :
    (⨅ i, (f i).ker).Normal :=
  Subgroup.normal_iInf_normal fun i ↦ MonoidHom.normal_ker (f i)

/-- **The opening sentence of the proof of `prop:mf-residual-calculus`, as one
closed proposition.**

The first clause is the printed sentence: an intersection of kernels is normal.
The second is the form the printed closure
`cl_MF^G(N) = ⋂{ker f : N ≤ ker f, f : G → M, M MF}` is written with, a
set-intersection; a kernel is normal by `MonoidHom.normal_ker`, which is how
`literalMFClosure_normal` obtains normality of that particular intersection. -/
def IntersectionOfKernelsIsNormal : Prop :=
  (∀ (G : Type u) [Group G] (Idx : Type v) (M : Idx → Type w)
      [∀ i, Group (M i)] (f : ∀ i, G →* M i), (⨅ i, (f i).ker).Normal) ∧
    (∀ (G : Type u) [Group G] (S : Set (Subgroup G)),
      (∀ K ∈ S, K.Normal) → (sInf S).Normal)

/-- Closed proof that an intersection of kernels is normal. -/
theorem manuscriptIntersectionOfKernelsIsNormal :
    IntersectionOfKernelsIsNormal := by
  constructor
  · intro G _ Idx M _ f
    exact iInf_ker_normal f
  · intro G _ S hS
    exact sInf_normal_of_forall_normal S hS

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
