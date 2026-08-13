import GroupApproximation.Sofic.CDEOperatorMF
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# MF C-star algebras and group embeddings

This file isolates the C-star-algebra formulation of the MF property.  An
algebra is MF when it admits a faithful complex star-algebra homomorphism into
a norm-matrix corona.  A group has an MF-algebra embedding when it embeds in
the unitary group of such an algebra.

No separability hypothesis is built into `IsMFAlgebra`: separability is a
size condition on the algebra, while the approximation property itself is the
faithful corona embedding.  This makes the definition usable for both the
usual separable algebras and ambient matrix coronas.
-/

namespace GroupApproximation

universe u v

/-- A star-algebra homomorphism, regarded as a star-monoid homomorphism. -/
def starAlgHomToStarMonoidHom
    {A : Type u} {B : Type v} [Semiring A] [Star A]
    [Semiring B] [Star B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →⋆ₐ[ℂ] B) : A →⋆* B where
  toFun := f
  map_one' := map_one f
  map_mul' := map_mul f
  map_star' := map_star f

/-- A complex C-star algebra is MF when it embeds faithfully in a quotient
`∏ M_(d n)(ℂ) / ⊕ M_(d n)(ℂ)` with positive matrix dimensions. -/
def IsMFAlgebra (A : Type u) [CStarAlgebra A] : Prop :=
  ∃ X : ℕ → FiniteModel, ∃ hne : ∀ n, Nonempty (X n),
    letI : ∀ n, Nonempty (X n) := hne
    (∀ n, 0 < Fintype.card (X n)) ∧
      StrictMono (fun n ↦ Fintype.card (X n)) ∧
        ∃ e : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n),
          Function.Injective e

/-- A norm-matrix corona is itself an MF algebra, witnessed by its identity
embedding. -/
theorem normMatrixCStarCorona_isMFAlgebra
    (X : ℕ → FiniteModel) (hne : ∀ n, Nonempty (X n))
    (hX : ∀ n, 0 < Fintype.card (X n))
    (hmono : StrictMono (fun n ↦ Fintype.card (X n))) :
    letI : ∀ n, Nonempty (X n) := hne
    IsMFAlgebra (NormMatrixCStarCorona (fun n ↦ X n)) := by
  letI : ∀ n, Nonempty (X n) := hne
  refine ⟨X, hne, hX, hmono, StarAlgHom.id ℂ _, ?_⟩
  intro a b hab
  change a = b at hab
  exact hab

/-- The group formulation through an arbitrary MF C-star algebra: the group
embeds faithfully in the algebra's unitary group. -/
def IsMFAlgebraEmbedding (G : Type u) [Group G] : Prop :=
  ∃ (A : Type) (inst : CStarAlgebra A),
    letI : CStarAlgebra A := inst
    IsMFAlgebra A ∧
      ∃ rho : G →* unitary A, Function.Injective rho

/-- The literal CDE corona embedding gives an MF-algebra embedding. -/
theorem IsCDEOperatorMF.isMFAlgebraEmbedding
    {G : Type u} [Group G] [Countable G]
    (h : IsCDEOperatorMF G) : IsMFAlgebraEmbedding G := by
  rcases h with ⟨X, hne, hX, hmono, rho, hrho⟩
  letI : ∀ n, Nonempty (X n) := hne
  refine ⟨NormMatrixCStarCorona (fun n ↦ X n), inferInstance, ?_⟩
  exact ⟨normMatrixCStarCorona_isMFAlgebra X hne hX hmono, rho, hrho⟩

/-- An embedding in the unitary group of an MF algebra composes with the
algebra's corona embedding to give the literal CDE embedding. -/
theorem IsMFAlgebraEmbedding.isCDEOperatorMF
    {G : Type u} [Group G] [Countable G]
    (h : IsMFAlgebraEmbedding G) : IsCDEOperatorMF G := by
  rcases h with ⟨A, inst, hA, rho, hrho⟩
  letI : CStarAlgebra A := inst
  rcases hA with ⟨X, hne, hX, hmono, e, he⟩
  letI : ∀ n, Nonempty (X n) := hne
  let ue : unitary A →* unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
    (Unitary.map (starAlgHomToStarMonoidHom e)).toMonoidHom
  exact ⟨X, hne, hX, hmono, ue.comp rho,
    (Unitary.map_injective he).comp hrho⟩

/-- For countable groups, embedding in an MF C-star algebra is exactly the
standard group-theoretic MF property. -/
theorem isMFAlgebraEmbedding_iff_isOperatorMF
    (G : Type u) [Group G] [Countable G] :
    IsMFAlgebraEmbedding G ↔ IsOperatorMF G := by
  rw [← isCDEOperatorMF_iff_isOperatorMF]
  exact ⟨IsMFAlgebraEmbedding.isCDEOperatorMF,
    IsCDEOperatorMF.isMFAlgebraEmbedding⟩

end GroupApproximation
