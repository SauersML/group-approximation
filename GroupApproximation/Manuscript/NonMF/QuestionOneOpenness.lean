import GroupApproximation.Manuscript.NonMF.QuestionAtoms
import GroupApproximation.Sofic.NormalKazhdanMFRadical
import GroupApproximation.Sofic.ActualCoronaMFRadical
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic

/-!
# Why the two formal reductions alone do not compute the residual

Earlier manuscript revisions asked for the exact value of `Res_MF(E)` and
observed that killing the marked involution and then the collapse defect did not,
by themselves, determine the residual of the final quotient.  This module
formalizes that limited statement: abstract reduction data are compatible with
targets carrying several different obstruction configurations and with both
trivial and nontrivial corona MF residual.

The manuscript now computes `Res_MF(E)` by adding paper-level information that
is deliberately absent here: a presentation of the final quotient, its embedding
in a symmetric amalgam, and Shulman's MF theorem.  Consequently the declarations
below remain valid tests of what the reductions alone imply, but they do not state
that the literal residual is open and must not be cited for that obsolete claim.

`IsReductionQuotient w S q` bundles a surjection killing `w` and the normal
closure of `S`.  No theorem below identifies its target with the manuscript's
literal final quotient or constructs one of the configurations inside that
quotient.  The product witnesses show only that those conclusions do not follow
from the abstract bundle in isolation.
-/

/-! ## Abstract reduction data -/

/-- **The two conclusions supplied by the abstract reductions.**

`q` is onto, it kills the distinguished word `w`, and it kills the normal
closure of the defect generators `S`:
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

/-! ## The reductions do not determine a residual without extra input -/

/-- **The reductions compute an equation, not a value.**

The two reduction conclusions are consistent with a target whose literal
genuine-corona MF radical is trivial and with a target whose radical is not, so
they do not determine the radical of the group they reduce to.  This is the
checkable content of the former reductions-only observation.

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
