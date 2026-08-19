import GroupApproximation.Manuscript.NonMF.QuestionAtoms
import GroupApproximation.Sofic.NormalKazhdanMFRadical
import GroupApproximation.Sofic.ActualCoronaMFRadical
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic

/-!
# Why Question 1 is a question: the two reductions exclude nothing

Ledger row `LI.12c`.  Question 1 of `\subsection*{Questions}` in
`non_mf_groups_exist.tex` asks what `Res_MF(E)` is, records that
`cor:collapsequot` computes it from `Res_MF((E/⟨w⟩)/D)`, records that the two
reductions detect nothing further, and then closes:

> That quotient may still contain a finite normal subgroup, a normal Kazhdan
> subgroup, or an orbit configuration to which the preceding criteria apply.

Nothing is claimed by that sentence and nothing could be.  It asserts only that
the two reductions leave the last group unconstrained — which is `LI.11` and
`LI.12`, formalized in `Manuscript.NonMF.QuestionAtoms` as
`signFreeQuotient_mark_eq_one` and `map_eq_one_of_mem_normalClosure` — and that
a further datum is therefore not excluded.  This file formalizes the second
half: *not excluded* is a non-implication, and a non-implication is refuted by
a witness.

## What is and is not proved here

`IsReductionQuotient w S q` bundles exactly the two conclusions the printed
sentence relies on: a surjection `q` that kills the distinguished word `w` and
kills the normal closure of the defect generators `S`.  The printed target
`(E/⟨w⟩)/D_coll` is one such quotient; **no theorem below is about it**, and
none constructs a configuration inside it.  What the theorems say is that the
reduction data cannot rule any configuration out, which is the exact strength
of the printed "may still".

* `reduction_does_not_exclude_finiteNormalSubgroup`,
  `reduction_does_not_exclude_normalKazhdanSubgroup` and
  `reduction_does_not_exclude_orbitConfiguration` refute, one apiece, the three
  implications the sentence declines to assert.  All three fall to the single
  witness of `exists_reductionQuotient_with_all_three_configurations`, and the
  witness is not degenerate: its `w` is a nonidentity element and its defect
  generating set contains one.
* `reduction_does_not_determine_residual` is the closing clause "so what
  `Res_MF(E)` is remains open" in its checkable form.  The reduction data are
  consistent with a target whose literal genuine-corona radical is trivial and
  with a target whose radical is not, so the two reductions compute an equation
  and not a value.  The nontrivial side is the manuscript's own sign-free
  quotient, at `LiteralSignFreeQuotient.actualCoronaMFResidual_ne_bot`.

## The three configurations

The sentence names `thm:criterion`, `thm:normal-kazhdan` and
`thm:projection-collapse`.  Each is transcribed below by its *group-side* datum
only — the data a quotient can be said to "contain":

* `thm:criterion` wants a finite normal subgroup, so
  `HasFiniteNormalSubgroup`;
* `thm:normal-kazhdan` wants a normal property-`(T)` subgroup, so
  `HasNormalKazhdanSubgroup`;
* `thm:projection-collapse` wants a property-`(T)` subgroup `L` and an element
  `s` with `sLs⁻¹ ⊆ L`, so `HasOrbitConfiguration`.  Its projection `p` lives in
  the target algebra, not in the group, and is deliberately not part of the
  predicate: a quotient does not contain a projection.

Each carries a nontriviality clause, for the reason recorded at `LI.14`: the
trivial subgroup satisfies all three vacuously and constrains no
representation, so a configuration predicate without `≠ ⊥` would be satisfied
by every group and would make the sentence contentless in the other direction.
-/

namespace GroupApproximation
namespace ManuscriptNonMF

/-! ## The reduction datum of Question 1 -/

/-- **The two conclusions Question 1 draws about its last quotient.**

`q` is onto, it kills the distinguished word `w`, and it kills the normal
closure of the defect generators `S`.  These are `LI.11` and `LI.12` exactly:
"`w = 1` in `E/⟨w⟩`, and the generators of `D` are trivial in the quotient
by `D`". -/
structure IsReductionQuotient {H : Type} [Group H] {Q : Type} [Group Q]
    (w : H) (S : Set H) (q : H →* Q) : Prop where
  /-- The reduction is a quotient map. -/
  surjective : Function.Surjective q
  /-- The distinguished word dies. -/
  mark_eq_one : q w = 1
  /-- The defect dies. -/
  defect_eq_one : ∀ x ∈ Subgroup.normalClosure S, q x = 1

/-! ## The three configurations the printed sentence names -/

/-- The group-side hypothesis of `thm:criterion`: a nontrivial finite normal
subgroup. -/
def HasFiniteNormalSubgroup (Q : Type) [Group Q] : Prop :=
  ∃ F : Subgroup Q, F.Normal ∧ Finite F ∧ F ≠ ⊥

/-- The group-side hypothesis of `thm:normal-kazhdan`: a nontrivial normal
property-`(T)` subgroup. -/
def HasNormalKazhdanSubgroup (Q : Type) [Group Q] : Prop :=
  ∃ K : Subgroup Q, K.Normal ∧ HasKazhdanPropertyT.{0, 0} K ∧ K ≠ ⊥

/-- The group-side hypothesis of `thm:projection-collapse`: a nontrivial
property-`(T)` subgroup `L` together with an element compressing it into
itself.  The theorem's projection is a datum of the target algebra and is not
part of this predicate. -/
def HasOrbitConfiguration (Q : Type) [Group Q] : Prop :=
  ∃ (L : Subgroup Q) (s : Q),
    HasKazhdanPropertyT.{0, 0} L ∧ (∀ gamma ∈ L, s * gamma * s⁻¹ ∈ L) ∧ L ≠ ⊥

/-- **Every nontrivial finite group carries all three configurations at once**,
with `⊤` as the subgroup and `1` as the compressing element.  Property `(T)`
comes from `hasKazhdanPropertyT_of_finite`, which is the manuscript's own
sentence "since finite groups have property (T), Theorem~\ref{thm:criterion} is
the finite case of Theorem~\ref{thm:normal-kazhdan}". -/
theorem configurations_of_finite_nontrivial :
    ∀ (Q : Type) [Group Q] [Finite Q] [Nontrivial Q],
      HasFiniteNormalSubgroup Q ∧ HasNormalKazhdanSubgroup Q ∧
        HasOrbitConfiguration Q := by
  intro Q _ _ _
  have htop : (⊤ : Subgroup Q) ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup Q)).mp inferInstance
  have hT : HasKazhdanPropertyT.{0, 0} (⊤ : Subgroup Q) :=
    hasKazhdanPropertyT_of_finite _
  exact ⟨⟨⊤, Subgroup.normal_top, inferInstance, htop⟩,
    ⟨⊤, Subgroup.normal_top, hT, htop⟩,
    ⟨⊤, 1, hT, fun gamma _ ↦ Subgroup.mem_top _, htop⟩⟩

/-! ## The witness: a reduction quotient onto an arbitrary group

The construction is the only one available at this strength, and it is honest
about what it shows.  Put the word and the defect generators in one factor of a
direct product and project onto the other: the reduction conclusions hold by
construction, the word and the generators stay nontrivial in the source, and
the target is arbitrary.  That is precisely "the reductions detect the elements
they detect, and say nothing about anything else". -/

/-- **The product reduction.**  For every `A`, every word `w : A`, every defect
generating set `S ⊆ A` and every target `Q`, the second projection of `A × Q`
is a reduction quotient for the copies of `w` and `S` in the first factor. -/
theorem sndHom_isReductionQuotient (A : Type) [Group A] (Q : Type) [Group Q]
    (w : A) (S : Set A) :
    IsReductionQuotient ((w, 1) : A × Q) ((fun a : A ↦ ((a, 1) : A × Q)) '' S)
      (MonoidHom.snd A Q) := by
  refine ⟨fun y ↦ ⟨(1, y), rfl⟩, rfl, ?_⟩
  intro x hx
  refine map_eq_one_of_mem_normalClosure (MonoidHom.snd A Q) ?_ hx
  rintro s ⟨t, -, rfl⟩
  rfl

/-- The copied word is still a nonidentity element of the source: the reduction
witness is not the degenerate one with `w = 1`. -/
theorem prod_mark_ne_one {A : Type} [Group A] (Q : Type) [Group Q] {w : A}
    (hw : w ≠ 1) : ((w, 1) : A × Q) ≠ 1 := fun h ↦ hw (Prod.mk_eq_one.mp h).1

/-- The two-element group, the smallest carrier of all three configurations. -/
abbrev TwoElementGroup : Type := Multiplicative (ZMod 2)

/-- **The witness.**  There is a reduction quotient — a surjection killing a
*nonidentity* word and the normal closure of a defect set containing a
*nonidentity* element — whose target contains a nontrivial finite normal
subgroup, a nontrivial normal Kazhdan subgroup, and an orbit configuration, all
three at once.

Nothing about the manuscript's own quotient follows from this, and nothing is
meant to.  What follows is that the two reductions do not exclude the three
criteria, which is what the printed sentence says. -/
theorem exists_reductionQuotient_with_all_three_configurations :
    ∃ (H : Type) (_ : Group H) (Q : Type) (_ : Group Q) (w : H) (S : Set H)
      (q : H →* Q),
      w ≠ 1 ∧ (∃ x ∈ S, x ≠ 1) ∧ IsReductionQuotient w S q ∧
        HasFiniteNormalSubgroup Q ∧ HasNormalKazhdanSubgroup Q ∧
        HasOrbitConfiguration Q := by
  obtain ⟨a, ha⟩ := exists_ne (1 : TwoElementGroup)
  obtain ⟨hfin, hkaz, horb⟩ := configurations_of_finite_nontrivial TwoElementGroup
  refine ⟨TwoElementGroup × TwoElementGroup, inferInstance, TwoElementGroup,
    inferInstance, (a, 1), (fun x : TwoElementGroup ↦ ((x, 1) : TwoElementGroup ×
      TwoElementGroup)) '' {a}, MonoidHom.snd _ _,
    prod_mark_ne_one _ ha, ⟨(a, 1), ⟨a, rfl, rfl⟩, prod_mark_ne_one _ ha⟩,
    sndHom_isReductionQuotient _ _ a {a}, hfin, hkaz, horb⟩

/-! ## The three non-implications -/

/-- **A finite normal subgroup is not excluded** (`thm:criterion`). -/
theorem reduction_does_not_exclude_finiteNormalSubgroup :
    ¬ ∀ (H : Type) [Group H] (Q : Type) [Group Q] (w : H) (S : Set H)
        (q : H →* Q),
        IsReductionQuotient w S q → ¬ HasFiniteNormalSubgroup Q := by
  intro h
  obtain ⟨H, instH, Q, instQ, w, S, q, -, -, hred, hfin, -, -⟩ :=
    exists_reductionQuotient_with_all_three_configurations
  exact @h H instH Q instQ w S q hred hfin

/-- **A normal Kazhdan subgroup is not excluded** (`thm:normal-kazhdan`). -/
theorem reduction_does_not_exclude_normalKazhdanSubgroup :
    ¬ ∀ (H : Type) [Group H] (Q : Type) [Group Q] (w : H) (S : Set H)
        (q : H →* Q),
        IsReductionQuotient w S q → ¬ HasNormalKazhdanSubgroup Q := by
  intro h
  obtain ⟨H, instH, Q, instQ, w, S, q, -, -, hred, -, hkaz, -⟩ :=
    exists_reductionQuotient_with_all_three_configurations
  exact @h H instH Q instQ w S q hred hkaz

/-- **An orbit configuration is not excluded** (`thm:projection-collapse`). -/
theorem reduction_does_not_exclude_orbitConfiguration :
    ¬ ∀ (H : Type) [Group H] (Q : Type) [Group Q] (w : H) (S : Set H)
        (q : H →* Q),
        IsReductionQuotient w S q → ¬ HasOrbitConfiguration Q := by
  intro h
  obtain ⟨H, instH, Q, instQ, w, S, q, -, -, hred, -, -, horb⟩ :=
    exists_reductionQuotient_with_all_three_configurations
  exact @h H instH Q instQ w S q hred horb

/-! ## "So what `Res_MF(E)` is remains open" -/

/-- **The reductions compute an equation, not a value.**

The two reduction conclusions are consistent with a target whose literal
genuine-corona MF radical is trivial and with a target whose radical is not, so
they do not determine the radical of the group they reduce to.  This is the
checkable content of the sentence that closes Question 1.

Both halves use the same product reduction, so neither is the degenerate `w = 1`
instance; the nontrivial half's target is the manuscript's own sign-free
quotient `E/⟨w⟩`, whose radical is nontrivial by
`LiteralSignFreeQuotient.actualCoronaMFResidual_ne_bot`. -/
theorem reduction_does_not_determine_residual :
    (∃ (H : Type) (_ : Group H) (Q : Type) (_ : Group Q) (w : H) (S : Set H)
        (q : H →* Q),
        w ≠ 1 ∧ IsReductionQuotient w S q ∧ actualCoronaMFResidual Q = ⊥) ∧
      (∃ (H : Type) (_ : Group H) (Q : Type) (_ : Group Q) (w : H) (S : Set H)
        (q : H →* Q),
        w ≠ 1 ∧ IsReductionQuotient w S q ∧ actualCoronaMFResidual Q ≠ ⊥) := by
  obtain ⟨a, ha⟩ := exists_ne (1 : TwoElementGroup)
  constructor
  · exact ⟨TwoElementGroup × PUnit.{1}, inferInstance, PUnit.{1}, inferInstance,
      (a, 1), (fun x : TwoElementGroup ↦ ((x, 1) : TwoElementGroup × PUnit.{1}))
        '' {a}, MonoidHom.snd _ _, prod_mark_ne_one _ ha,
      sndHom_isReductionQuotient _ _ a {a}, Subsingleton.elim _ _⟩
  · exact ⟨TwoElementGroup × LiteralSignFreeQuotient.SignFreeQuotient,
      inferInstance, LiteralSignFreeQuotient.SignFreeQuotient, inferInstance,
      (a, 1), (fun x : TwoElementGroup ↦ ((x, 1) : TwoElementGroup ×
        LiteralSignFreeQuotient.SignFreeQuotient)) '' {a}, MonoidHom.snd _ _,
      prod_mark_ne_one _ ha, sndHom_isReductionQuotient _ _ a {a},
      LiteralSignFreeQuotient.actualCoronaMFResidual_ne_bot⟩

end ManuscriptNonMF
end GroupApproximation
