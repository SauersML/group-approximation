import GroupApproximation.GGT.HullSCAuxiliaryRelatorPublished
import GroupApproximation.GGT.HullSCLemma44RelativeIsoperimetric
import GroupApproximation.Meta.AxiomGuard

/-!
# The boundedness hypothesis in the published Hull Lemma 4.4

Hull's strongly bounded family has uniformly bounded relator lengths as well
as finite peripheral-letter support. The historical `IsLemma44Input` contains
only the second clause. It is preserved verbatim; the explicit strengthening
below restores the missing clause (issue #201).

Every actual one-relator symmetrized family has this stronger boundedness.
The full auxiliary-relator producer supplies it without an extra assumption.
The corrected area-transfer statement remains a proof obligation; this file
does not assert that the relative-presentation geometry has been proved.
-/

namespace GroupApproximation.HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

namespace RelWord

/-- Both clauses of Hull's strong boundedness, with a common length bound
chosen before the relator. -/
structure IsStronglyBounded {G : Type u} [Group G] {Λ : Type w}
    (W : Set (List (GGT.RelLetter G Λ))) : Prop where
  lengthBounded : ∃ L : ℕ, ∀ word ∈ W, word.length ≤ L
  finiteComponentLetters :
    {a : GGT.RelLetter G Λ |
      (∃ lam h, a = GGT.RelLetter.comp lam h) ∧ ∃ word ∈ W, a ∈ word}.Finite

/-- An explicit strengthening of the original input, leaving its definition
and all its existing consequences unchanged. -/
structure IsBoundedLemma44Input {G : Type u} [Group G] {Λ : Type w}
    (D : GGT.RelGenSet G Λ) (W : Set (List (GGT.RelLetter G Λ)))
    (eps : ℕ) (mu : ℝ) (rho : ℕ) : Prop extends IsLemma44Input D W eps mu rho where
  lengthBounded : ∃ L : ℕ, ∀ word ∈ W, word.length ≤ L

theorem IsBoundedLemma44Input.isStronglyBounded
    {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ} {W : Set (List (GGT.RelLetter G Λ))}
    {eps rho : ℕ} {mu : ℝ} (h : IsBoundedLemma44Input D W eps mu rho) :
    IsStronglyBounded W := ⟨h.lengthBounded, h.stronglyBounded⟩

theorem isStronglyBounded_symmetrized
    {G : Type u} [Group G] {Λ : Type w}
    (r : List (GGT.RelLetter G Λ)) : IsStronglyBounded (symmetrized r) := by
  refine ⟨⟨r.length, ?_⟩, finite_componentLetters_symmetrized r⟩
  intro word hword
  exact (Sym.length_eq (mem_symmetrized.mp hword)).le

theorem IsLemma44Input.bounded_symmetrized
    {G : Type u} [Group G] {Λ : Type w} {D : GGT.RelGenSet G Λ}
    {r : List (GGT.RelLetter G Λ)} {eps rho : ℕ} {mu : ℝ}
    (h : IsLemma44Input D (symmetrized r) eps mu rho) :
    IsBoundedLemma44Input D (symmetrized r) eps mu rho :=
  ⟨h, (isStronglyBounded_symmetrized r).lengthBounded⟩

theorem IsBoundedLemma44Input.mono_parameters
    {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ} {W : Set (List (GGT.RelLetter G Λ))}
    {eps eps' rho rho' : ℕ} {mu mu' : ℝ}
    (h : IsBoundedLemma44Input D W eps mu rho)
    (heps : eps' ≤ eps) (hmu : mu ≤ mu') (hrho : rho' ≤ rho) :
    IsBoundedLemma44Input D W eps' mu' rho' :=
  ⟨h.toIsLemma44Input.mono_parameters heps hmu hrho, h.lengthBounded⟩

end RelWord

/-- The exact relator already used by the manuscript supplies the full
published boundedness condition, including its uniform length bound. -/
theorem AuxiliaryPeripheralFamily.exists_stronglyBoundedRelatorPublished_exact
    {G : Type u} [Group G] {A : HullGeneratingSet G}
    {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (D : AuxiliaryPeripheralFamily A N S) (hN : Suitable A.alphabet N)
    (t : G) (ht : t⁻¹ ∈ D.rel.base) (eps rho : ℕ) (mu : ℝ) (hmu : 0 < mu) :
    ∃ u ∈ N, ∃ R : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)),
      GGT.RelLetter.listVal R = t⁻¹ * u ∧
        RelWord.IsLemma49Input D.rel (RelWord.symmetrized R) eps mu rho ∧
        RelWord.IsBoundedLemma44Input D.rel (RelWord.symmetrized R) eps mu rho := by
  obtain ⟨u, hu, R, hval, hsc⟩ :=
    D.exists_auxiliaryRelatorOfBaseLetterPublished_exact hN t ht eps rho mu hmu
  exact ⟨u, hu, R, hval, hsc, hsc.toIsLemma44Input.bounded_symmetrized⟩

/-- The corrected area-transfer obligation. Its admissible relators are
strongly bounded in the published sense and are killed by the quotient.
The conclusion is hyperbolic embeddedness itself: pullback into the original
source relative balls can fail when those balls omit the finite peripheral
letters occurring in the filling. No proof of this statement is claimed here. -/
def BoundedRelativeLinearAreaTransferStatement : Prop :=
  ∀ {G : Type u} [Group G] {Λ : Type w} (D : GGT.RelGenSet G Λ),
    D.IsHyperbolicallyEmbedded →
    ∀ (W : Set (List (GGT.RelLetter G Λ))) {Q : Type v} [Group Q]
      (q : G →* Q) (hq : Function.Surjective q),
      (∀ word ∈ W, RelWord.IsAdmissible D word) →
      RelWord.IsStronglyBounded W →
      (∀ word ∈ W, q (GGT.RelLetter.listVal word) = 1) →
      RelativeLinearKernelArea D W q →
        (D.mapSurjective q hq).IsHyperbolicallyEmbedded

end GroupApproximation.HullSC

#audit_axioms GroupApproximation.HullSC.RelWord.isStronglyBounded_symmetrized
#audit_axioms GroupApproximation.HullSC.RelWord.IsBoundedLemma44Input.mono_parameters
#audit_axioms GroupApproximation.HullSC.AuxiliaryPeripheralFamily.exists_stronglyBoundedRelatorPublished_exact
