import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Mixed identities that no finite set normally generates

`mixedIdentities G n` is the subgroup `J_G(G ∗ F_n)` of Belk–Fournier-Facio–Hyde–Zaremsky
(arXiv:2503.21882v2), Question 3.3: the intersection of the kernels of all homomorphisms
`G ∗ F_n → G` that restrict to the identity on `G`. The definition is a byte-identical copy of the
shared block of `Palomar/BooneHigmanChallenge.lean`, so a statement about it here closes the
challenge statement by `exact`.

* `mem_mixedIdentities`: `w` is a mixed identity iff every retraction `G ∗ F_n → G` kills it.
* `not_isFinitelyNormallyGenerated_of_separating`: suppose that for every finite set `S` of mixed
  identities there is a homomorphism `φ` from `G ∗ F_n` to some group that kills `S` but not some
  mixed identity. Then `J_G(G ∗ F_n)` is not the normal closure of a finite set. The homomorphism
  kills the normal closure of `S`, so the normal closure of `S` misses that mixed identity.
-/

namespace GroupApproximation
namespace BHPalomar
namespace MixedIdentities

/-- The mixed identities `J_G(G ∗ F_n)`: the intersection of the kernels of all
homomorphisms `G ∗ F_n → G` that restrict to the identity on `G`. -/
def mixedIdentities (G : Type) [Group G] (n : ℕ) :
    Subgroup (Monoid.Coprod G (FreeGroup (Fin n))) :=
  ⨅ (φ : Monoid.Coprod G (FreeGroup (Fin n)) →* G)
    (_ : φ.comp Monoid.Coprod.inl = MonoidHom.id G), φ.ker

theorem mem_mixedIdentities {G : Type} [Group G] {n : ℕ}
    {w : Monoid.Coprod G (FreeGroup (Fin n))} :
    w ∈ mixedIdentities G n ↔
      ∀ φ : Monoid.Coprod G (FreeGroup (Fin n)) →* G,
        φ.comp Monoid.Coprod.inl = MonoidHom.id G → φ w = 1 := by
  simp only [mixedIdentities, Subgroup.mem_iInf, MonoidHom.mem_ker]

/-- **Separation kills finite normal generation.** If every finite set of mixed identities is
killed by a homomorphism that does not kill some mixed identity, then the mixed identities are
not the normal closure of a finite set. -/
theorem not_isFinitelyNormallyGenerated_of_separating {G H : Type} [Group G] [Group H] {n : ℕ}
    (hsep : ∀ S : Set (Monoid.Coprod G (FreeGroup (Fin n))), S.Finite →
      S ⊆ (mixedIdentities G n : Set (Monoid.Coprod G (FreeGroup (Fin n)))) →
      ∃ φ : Monoid.Coprod G (FreeGroup (Fin n)) →* H, (∀ v ∈ S, φ v = 1) ∧
        ∃ w ∈ mixedIdentities G n, φ w ≠ 1) :
    ¬ (mixedIdentities G n).IsFinitelyNormallyGenerated := by
  rintro ⟨S, hSfin, hS⟩
  have hSJ : S ⊆ (mixedIdentities G n : Set (Monoid.Coprod G (FreeGroup (Fin n)))) := by
    rw [← hS]
    exact Subgroup.subset_normalClosure
  obtain ⟨φ, hφS, w, hw, hφw⟩ := hsep S hSfin hSJ
  have hle : Subgroup.normalClosure S ≤ φ.ker :=
    Subgroup.normalClosure_le_normal fun v hv => (MonoidHom.mem_ker).mpr (hφS v hv)
  rw [hS] at hle
  exact hφw ((MonoidHom.mem_ker).mp (hle hw))

#audit_axioms GroupApproximation.BHPalomar.MixedIdentities.mem_mixedIdentities
#audit_axioms GroupApproximation.BHPalomar.MixedIdentities.not_isFinitelyNormallyGenerated_of_separating

end MixedIdentities
end BHPalomar
end GroupApproximation
