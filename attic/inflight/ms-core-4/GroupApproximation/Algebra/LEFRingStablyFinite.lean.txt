import GroupApproximation.Algebra.DirectlyFiniteReflection
import GroupApproximation.Sofic.LocallyFiniteMF
import GroupApproximation.Meta.AxiomGuard

/-!
# LEF rings are stably finite; their general linear groups are LEF, and MF when countable

`non_mf_groups_exist.tex`, section `sec:chain-core`, tex 1354–1362:

> A ring is \emph{LEF} if every finite subset admits an injective map into a finite ring preserving
> the additions and multiplications that stay in that subset, and preserving $0$ and $1$ when
> present.  A group is LEF with the analogous multiplicative definition.  Finite inverse-pair tables
> show that LEF rings are stably finite.  Entrywise finite ring models, including the entries of
> inverse matrices, show that their general linear groups are LEF.  Countable LEF groups are MF, by
> the regular representations of the finite groups in their local models.

The ring notion is `Pestov91.IsLEFRing`, the group notion `IsLEF`, and "MF" is `IsOperatorMF`.

* `Pestov91.IsLEFRing.isDedekindFiniteMonoid`: the finite inverse-pair table `{a, b, b a, 1}`.
  Its finite model sends `a b = 1` to `φ a φ b = 1`.  A finite ring is directly finite, so
  `φ (b a) = φ b φ a = 1 = φ 1`, and injectivity on the table gives `b a = 1`.
* `Pestov91.IsLEFRing.isStablyFiniteRing`: the same argument in `M_n(A)`, which is LEF by
  `Pestov91.IsLEFRing.matrix`.
* `lefStablyFiniteInterface`: the producer of chain-reflection's `LEFStablyFiniteInterface`.
* `Pestov91.IsLEFRing.isLEF_generalLinear`: `M_n(A)` is LEF entrywise (`IsLEFRing.matrix`), and
  `IsLEFRing.isLEF_units` puts the entries of inverse matrices into the table.
* `printedCountableLEFGroupsMF`: `isOperatorMF_of_isLEF`, whose weak-MF step
  (`isWeakMF_of_isLEF`) uses the permutation matrices of the left regular action of each finite
  local model.
* Closed endpoints: `printedLEFRingsStablyFinite`, `printedGeneralLinearGroupsOfLEFRingsLEF`,
  `printedCountableLEFGroupsMF`.
-/

namespace GroupApproximation

universe w

namespace Pestov91

/-- **An LEF ring is directly finite** (tex 1358–1359, "Finite inverse-pair tables show that LEF
rings are stably finite", the `1 × 1` case).  The finite table is `{a, b, b a, 1}`. -/
theorem IsLEFRing.isDedekindFiniteMonoid {A : Type*} [Ring A] (hA : IsLEFRing A) :
    IsDedekindFiniteMonoid A := by
  classical
  refine ⟨fun {a b} hab ↦ ?_⟩
  obtain ⟨F, _, _, φ, hinj, -, h1, hφ⟩ := hA ({a, b, b * a, 1} : Finset A)
  have ha : a ∈ ({a, b, b * a, 1} : Finset A) := by simp
  have hb : b ∈ ({a, b, b * a, 1} : Finset A) := by simp
  have hba : b * a ∈ ({a, b, b * a, 1} : Finset A) := by simp
  have hone : (1 : A) ∈ ({a, b, b * a, 1} : Finset A) := by simp
  have hF : φ a * φ b = 1 := by rw [← (hφ a ha b hb).2, hab, h1]
  have hF' : φ b * φ a = 1 := mul_eq_one_symm hF
  refine hinj hba hone ?_
  rw [(hφ b hb a ha).2, hF', h1]

/-- **LEF rings are stably finite** (tex 1358–1359): every `M_n(A)` is LEF by
`IsLEFRing.matrix`, hence directly finite by `IsLEFRing.isDedekindFiniteMonoid`. -/
theorem IsLEFRing.isStablyFiniteRing {A : Type*} [Ring A] (hA : IsLEFRing A) :
    IsStablyFiniteRing A :=
  ⟨fun n ↦ (hA.matrix (Fin n)).isDedekindFiniteMonoid⟩

/-- **General linear groups of an LEF ring are LEF** (tex 1359–1360, "Entrywise finite ring
models, including the entries of inverse matrices, show that their general linear groups are
LEF"). -/
theorem IsLEFRing.isLEF_generalLinear {A : Type*} [Ring A] (hA : IsLEFRing A) (n : Type)
    [Fintype n] [DecidableEq n] : IsLEF (Matrix n n A)ˣ :=
  (hA.matrix n).isLEF_units

/-- **General linear groups of a countable LEF ring are MF** (tex 1359–1362). -/
theorem IsLEFRing.isOperatorMF_generalLinear {A : Type*} [Ring A] [Countable A]
    (hA : IsLEFRing A) (n : Type) [Fintype n] [DecidableEq n] :
    IsOperatorMF (Matrix n n A)ˣ := by
  haveI : Countable (Matrix n n A) := inferInstanceAs (Countable (n → n → A))
  haveI : Countable (Matrix n n A)ˣ := Function.Injective.countable Units.val_injective
  exact isOperatorMF_of_isLEF (hA.isLEF_generalLinear n)

end Pestov91

/-- **Producer of `LEFStablyFiniteInterface`** (chain-reflection's residual; tex 1529–1530,
"Since $R_Y$ itself is LEF and therefore stably finite"). -/
theorem lefStablyFiniteInterface : LEFStablyFiniteInterface.{w} :=
  fun _ _ hB ↦ hB.isStablyFiniteRing

/-- **tex 1358–1359**, "Finite inverse-pair tables show that LEF rings are stably finite." -/
def PrintedLEFRingsStablyFinite : Prop :=
  ∀ (A : Type) [Ring A], Pestov91.IsLEFRing A → IsStablyFiniteRing A

theorem printedLEFRingsStablyFinite : PrintedLEFRingsStablyFinite :=
  fun _ _ hA ↦ hA.isStablyFiniteRing

/-- **tex 1359–1360**, "Entrywise finite ring models, including the entries of inverse matrices,
show that their general linear groups are LEF." -/
def PrintedGeneralLinearGroupsOfLEFRingsLEF : Prop :=
  ∀ (A : Type) [Ring A], Pestov91.IsLEFRing A → ∀ n : ℕ, IsLEF (Matrix (Fin n) (Fin n) A)ˣ

theorem printedGeneralLinearGroupsOfLEFRingsLEF : PrintedGeneralLinearGroupsOfLEFRingsLEF :=
  fun _ _ hA n ↦ hA.isLEF_generalLinear (Fin n)

/-- **tex 1361–1362**, "Countable LEF groups are MF, by the regular representations of the
finite groups in their local models." -/
def PrintedCountableLEFGroupsMF : Prop :=
  ∀ (G : Type) [Group G] [Countable G], IsLEF G → IsOperatorMF G

theorem printedCountableLEFGroupsMF : PrintedCountableLEFGroupsMF :=
  fun _ _ _ hG ↦ isOperatorMF_of_isLEF hG

end GroupApproximation

open GroupApproximation

#audit_closed_axioms GroupApproximation.printedLEFRingsStablyFinite
#audit_closed_axioms GroupApproximation.printedGeneralLinearGroupsOfLEFRingsLEF
#audit_closed_axioms GroupApproximation.printedCountableLEFGroupsMF
#audit_closed_axioms GroupApproximation.lefStablyFiniteInterface
#audit_axioms GroupApproximation.Pestov91.IsLEFRing.isOperatorMF_generalLinear
