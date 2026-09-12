import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.ResiduallyFinite
import GroupApproximation.Sofic.LocallyFiniteMF

/-!
# Finitely generated abelian groups are residually finite, and countable abelian groups are MF

`non_mf_groups_exist.tex`, inside the proof of Theorem `thm:mf-quotient-units`:

> A countable abelian group `A` is MF.

The printed justification is analytic --- `C*_max(A)` is commutative and
separable, hence residually finite-dimensional and MF, citing
Brown--Kirchberg.  This module proves the same statement instead, with no
literature input, along the group-theoretic route: a countable abelian group is
LEF because its finitely generated subgroups are residually finite, and LEF
groups are MF (`Sofic.isOperatorMF_of_isLEF`).

## Why a bespoke separation predicate

Mathlib has `Group.ResiduallyFinite` with instances for finite groups, for
subgroups, and for binary products, and the criterion
`residuallyFinite_of_forall_exists_finite_monoidHom`.  What it does not have is
residual finiteness of finitely generated abelian groups, and the structure
theorem it must go through, `AddCommGroup.equiv_free_prod_directSum_zmod`, is
stated additively while the target here is multiplicative.

Rather than carry a group's worth of `Additive`/`Multiplicative` class
transport, everything below is phrased with `AddSeparated`: the plain
proposition that every nonzero element is detected by some homomorphism to some
finite additive group.  It needs no class API, transports along `AddEquiv` in
one line, and is converted to `Group.ResiduallyFinite` exactly once, at the end,
through `residuallyFinite_of_forall_exists_finite_monoidHom`.

The free part is handled without any induction or product decomposition: a
nonzero element of `Fin n →₀ ℤ` is nonzero in some coordinate, and that single
coordinate is separated in `ℤ` by reduction modulo `|g i| + 1`.
-/

namespace GroupApproximation
namespace MFQuotientUnits

/-! ### The separation predicate -/

/-- Every nonzero element is detected by a homomorphism to a finite additive
group.  Stated without a class so that no additive `ResiduallyFinite` API is
needed. -/
def AddSeparated (G : Type) [AddGroup G] : Prop :=
  ∀ g : G, g ≠ 0 →
    ∃ (H : Type) (_ : AddGroup H) (_ : Finite H) (f : G →+ H), f g ≠ 0

theorem addSeparated_of_finite (G : Type) [AddGroup G] [Finite G] :
    AddSeparated G := fun _ hg ↦
  ⟨G, inferInstance, inferInstance, AddMonoidHom.id G, hg⟩

theorem AddSeparated.of_addEquiv {G G' : Type} [AddGroup G] [AddGroup G']
    (e : G ≃+ G') (h : AddSeparated G') : AddSeparated G := by
  intro g hg
  obtain ⟨H, hH, hfin, f, hf⟩ := h (e g) (by
    intro hcon
    exact hg (by simpa using congrArg e.symm hcon))
  exact ⟨H, hH, hfin, f.comp e.toAddMonoidHom, hf⟩

theorem AddSeparated.prod {G G' : Type} [AddGroup G] [AddGroup G']
    (h : AddSeparated G) (h' : AddSeparated G') : AddSeparated (G × G') := by
  intro g hg
  by_cases hfst : g.1 = 0
  · have hsnd : g.2 ≠ 0 := by
      intro hcon
      exact hg (Prod.ext hfst hcon)
    obtain ⟨H, hH, hfin, f, hf⟩ := h' g.2 hsnd
    exact ⟨H, hH, hfin, f.comp (AddMonoidHom.snd G G'), hf⟩
  · obtain ⟨H, hH, hfin, f, hf⟩ := h g.1 hfst
    exact ⟨H, hH, hfin, f.comp (AddMonoidHom.fst G G'), hf⟩

/-! ### The integers -/

/-- **`ℤ` is separated**: reduction modulo `|g| + 1` detects `g`. -/
theorem addSeparated_int : AddSeparated ℤ := by
  intro g hg
  haveI : NeZero (g.natAbs + 1) := ⟨Nat.succ_ne_zero _⟩
  refine ⟨ZMod (g.natAbs + 1), inferInstance, inferInstance,
    Int.castAddHom (ZMod (g.natAbs + 1)), ?_⟩
  intro hcon
  have hdvd : ((g.natAbs + 1 : ℕ) : ℤ) ∣ g := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hcon
  have habspos : (0 : ℤ) < |g| := abs_pos.mpr hg
  have hle : ((g.natAbs + 1 : ℕ) : ℤ) ≤ |g| :=
    Int.le_of_dvd habspos ((dvd_abs _ _).mpr hdvd)
  have habs : |g| = (g.natAbs : ℤ) := Int.abs_eq_natAbs g
  rw [habs] at hle
  omega

/-- **A finitely supported family of integers is separated**: it is nonzero in
some coordinate, and that coordinate is separated in `ℤ`. -/
theorem addSeparated_finsupp_int (n : ℕ) : AddSeparated (Fin n →₀ ℤ) := by
  intro g hg
  have hex : ∃ i, g i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hg (Finsupp.ext hcon)
  obtain ⟨i, hi⟩ := hex
  obtain ⟨H, hH, hfin, f, hf⟩ := addSeparated_int (g i) hi
  exact ⟨H, hH, hfin, f.comp (Finsupp.applyAddHom i), hf⟩

/-! ### Finitely generated abelian groups -/

/-- **Every finitely generated abelian group is separated.**  This is the
structure theorem: the free part is `addSeparated_finsupp_int`, the torsion part
is finite, and the product of two separated groups is separated. -/
theorem addSeparated_of_fg (G : Type) [AddCommGroup G] [AddGroup.FG G] :
    AddSeparated G := by
  obtain ⟨n, ι, hι, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod G
  haveI : Fintype ι := hι
  haveI hne : ∀ i, NeZero (p i ^ e i) := by
    intro i
    refine ⟨?_⟩
    exact pow_ne_zero _ (hp i).ne_zero
  haveI : Finite (DirectSum ι (fun i ↦ ZMod (p i ^ e i))) := by
    have hpi : Finite (∀ i : ι, ZMod (p i ^ e i)) := inferInstance
    exact Finite.of_equiv _
      (DFinsupp.equivFunOnFintype (β := fun i ↦ ZMod (p i ^ e i))).symm
  exact AddSeparated.of_addEquiv f
    ((addSeparated_finsupp_int n).prod
      (addSeparated_of_finite (DirectSum ι (fun i ↦ ZMod (p i ^ e i)))))

/-- **Every finitely generated abelian group is residually finite.**  The
`Additive` detour is confined to this proof. -/
theorem residuallyFinite_of_fg_commGroup (A : Type) [CommGroup A] [Group.FG A] :
    Group.ResiduallyFinite A := by
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  have hga : (Additive.ofMul g : Additive A) ≠ 0 := by
    intro hcon
    exact hg (by simpa using hcon)
  obtain ⟨H, hH, hfin, f, hf⟩ := addSeparated_of_fg (Additive A) _ hga
  refine ⟨Multiplicative H, inferInstance, inferInstance,
    AddMonoidHom.toMultiplicative f, ?_⟩
  intro hcon
  exact hf hcon

/-! ### Countable abelian groups are MF -/

/-- Every finite subset of an abelian group lies in a residually finite
subgroup: the subgroup it generates. -/
theorem isLEF_of_commGroup (A : Type) [CommGroup A] [Countable A] : IsLEF A := by
  classical
  refine isLEF_of_forall_finset_residuallyFinite ?_
  intro s
  refine ⟨Subgroup.closure (s : Set A), fun x hx ↦ Subgroup.subset_closure hx, ?_⟩
  haveI : Group.FG (Subgroup.closure (s : Set A)) :=
    (Group.fg_iff_subgroup_fg _).mpr ⟨s, rfl⟩
  exact residuallyFinite_of_fg_commGroup _

/-- **The printed "a countable abelian group `A` is MF".**  Proved rather than
quoted: the printed justification runs through residual finite-dimensionality of
`C*_max(A)` and Brown--Kirchberg, and this one runs through LEF instead. -/
theorem isOperatorMF_of_commGroup_countable (A : Type) [CommGroup A]
    [Countable A] : IsOperatorMF A :=
  isOperatorMF_of_isLEF (isLEF_of_commGroup A)

end MFQuotientUnits
end GroupApproximation
