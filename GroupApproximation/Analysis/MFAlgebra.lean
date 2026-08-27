import GroupApproximation.Sofic.CDEOperatorMF
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Topology.Bases

/-!
# MF C-star algebras and group embeddings

For a separable complex C-star algebra, the Blackadar--Kirchberg MF property
is faithful embeddability into a norm-matrix corona.  The embedding need not
be unital.  We therefore distinguish two predicates:

* `HasMFEmbedding A` is the bare corona-embedding property, with no
  separability assertion.  It applies in particular to the generally
  nonseparable corona itself.
* `IsMFAlgebra A` is the literature-standard property: separability together
  with `HasMFEmbedding A`.

The distinction prevents the ambient corona from being mislabeled as an MF
algebra merely because it embeds into itself.

For the implication from an MF group C-star algebra to an MF group, a
possibly nonunital embedding `e` is enough.  Its restriction to unitaries is
made unital by the canonical corner-complement correction

`u ↦ e(u) + (1 - e(1))`.

This construction is formalized below rather than silently assuming that the
C-star embedding preserves the unit.
-/

namespace GroupApproximation

universe u v

/-- Bare Blackadar--Kirchberg corona embeddability.  This predicate contains
no separability assertion and allows the faithful star homomorphism to be
nonunital, as in the standard notion of a C-star subalgebra. -/
def HasMFEmbedding (A : Type u) [NonUnitalCStarAlgebra A] : Prop :=
  ∃ X : ℕ → FiniteModel, ∃ hne : ∀ n, Nonempty (X n),
    letI : ∀ n, Nonempty (X n) := hne
    (∀ n, 0 < Fintype.card (X n)) ∧
      StrictMono (fun n ↦ Fintype.card (X n)) ∧
        ∃ e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n),
          Function.Injective e

/-- The Blackadar--Kirchberg MF property for a complex C-star algebra:
separability and a faithful, possibly nonunital, star homomorphism into a
norm-matrix corona. -/
def IsMFAlgebra (A : Type u) [NonUnitalCStarAlgebra A] : Prop :=
  TopologicalSpace.SeparableSpace A ∧ HasMFEmbedding A

/-! ## Heredity under faithful star homomorphisms -/

/-- Bare MF embeddability passes backward along an injective nonunital star
homomorphism.  Compose the faithful map into the MF algebra with its faithful
norm-matrix-corona representation. -/
theorem HasMFEmbedding.of_injective_nonUnitalStarAlgHom
    {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (hB : HasMFEmbedding B) (i : A →⋆ₙₐ[ℂ] B)
    (hi : Function.Injective i) : HasMFEmbedding A := by
  rcases hB with ⟨X, hXne, hXpos, hXmono, e, he⟩
  letI : ∀ n, Nonempty (X n) := hXne
  exact ⟨X, hXne, hXpos, hXmono, e.comp i, he.comp hi⟩

/-- The MF property of separable C-star algebras is hereditary under faithful
star homomorphisms.  Separability of the source follows because an injective
star homomorphism between C-star algebras is an isometric embedding, and every
subspace of a second-countable space is separable. -/
theorem IsMFAlgebra.of_injective_nonUnitalStarAlgHom
    {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (hB : IsMFAlgebra B) (i : A →⋆ₙₐ[ℂ] B)
    (hi : Function.Injective i) : IsMFAlgebra A := by
  letI : TopologicalSpace.SeparableSpace B := hB.1
  refine ⟨(NonUnitalStarAlgHom.isometry i hi).isEmbedding.separableSpace, ?_⟩
  exact hB.2.of_injective_nonUnitalStarAlgHom i hi

/-- A norm-matrix corona has the bare MF embedding property, witnessed by
its identity map.  No separability claim is made. -/
theorem normMatrixCStarCorona_hasMFEmbedding
    (X : ℕ → FiniteModel) (hne : ∀ n, Nonempty (X n)) :
    (hX : ∀ n, 0 < Fintype.card (X n)) →
    (hmono : StrictMono (fun n ↦ Fintype.card (X n))) →
      letI : ∀ n, Nonempty (X n) := hne
      HasMFEmbedding (NormMatrixCStarCorona (fun n ↦ X n)) := by
  intro hX hmono
  letI : ∀ n, Nonempty (X n) := hne
  refine ⟨X, hne, hX, hmono, NonUnitalStarAlgHom.id ℂ _, ?_⟩
  intro a b hab
  change a = b at hab
  exact hab

/-- A nonunital star homomorphism sends a unitary to a unitary after
adjoining the complement of the image of the source unit. -/
noncomputable def nonUnitalStarAlgHomUnitaryMap
    {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    (e : A →⋆ₙₐ[ℂ] B) : unitary A →* unitary B where
  toFun u := ⟨e (u : A) + (1 - e 1), by
    let x : B := e (u : A)
    let p : B := e 1
    have hp_star : star p = p := by
      change star (e 1) = e 1
      rw [← map_star]
      simp
    have hp_mul : p * p = p := by
      change e 1 * e 1 = e 1
      rw [← map_mul]
      simp
    have hpx : p * x = x := by
      change e 1 * e (u : A) = e (u : A)
      rw [← map_mul]
      simp
    have hxp : x * p = x := by
      change e (u : A) * e 1 = e (u : A)
      rw [← map_mul]
      simp
    have hstarxp : star x * p = star x := by
      have h := congrArg star hpx
      simpa only [star_mul, hp_star, star_star] using h
    have hpstarx : p * star x = star x := by
      have h := congrArg star hxp
      simpa only [star_mul, hp_star, star_star] using h
    have hstarx_mul_x : star x * x = p := by
      change star (e (u : A)) * e (u : A) = e 1
      rw [← map_star, ← map_mul]
      exact congrArg e u.property.1
    have hx_mul_starx : x * star x = p := by
      change e (u : A) * star (e (u : A)) = e 1
      rw [← map_star, ← map_mul]
      exact congrArg e u.property.2
    change
      star (x + (1 - p)) * (x + (1 - p)) = 1 ∧
        (x + (1 - p)) * star (x + (1 - p)) = 1
    rw [star_add, star_sub, star_one, hp_star]
    constructor <;>
      simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul,
        hstarxp, hpstarx, hpx, hxp, hp_mul, hstarx_mul_x,
        hx_mul_starx] <;>
      noncomm_ring⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Subtype.ext
    change e ((u : A) * (v : A)) + (1 - e 1) =
      (e (u : A) + (1 - e 1)) * (e (v : A) + (1 - e 1))
    rw [map_mul]
    have hu : e (u : A) * e 1 = e (u : A) := by
      rw [← map_mul]
      simp
    have hv : e 1 * e (v : A) = e (v : A) := by
      rw [← map_mul]
      simp
    have hp : e 1 * e 1 = e 1 := by
      rw [← map_mul]
      simp
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul,
      hu, hv, hp]
    noncomm_ring

/-- Injectivity on the source algebra implies injectivity of the corrected
unitary-group homomorphism. -/
theorem nonUnitalStarAlgHomUnitaryMap_injective
    {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    {e : A →⋆ₙₐ[ℂ] B} (he : Function.Injective e) :
    Function.Injective (nonUnitalStarAlgHomUnitaryMap e) := by
  intro a b hab
  apply Subtype.ext
  apply he
  have h := congrArg Subtype.val hab
  exact add_right_cancel h

/-- A faithful group embedding into the unitary group of an algebra with a
bare MF embedding gives the literal CDE group property. -/
theorem HasMFEmbedding.isCDEOperatorMF
    {G : Type u} [Group G] [Countable G]
    {A : Type v} [CStarAlgebra A]
    (hA : HasMFEmbedding A)
    (rho : G →* unitary A) (hrho : Function.Injective rho) :
    IsCDEOperatorMF G := by
  rcases hA with ⟨X, hne, hX, _hmono, e, he⟩
  letI : ∀ n, Nonempty (X n) := hne
  let rhoCStar : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
    (nonUnitalStarAlgHomUnitaryMap e).comp rho
  let rhoSequence : G →* NormMatrixCoronaUnitary X :=
    (normMatrixCoronaUnitaryEquiv X).symm.toMonoidHom.comp rhoCStar
  have hop : IsOperatorMF G :=
    ⟨X, hX, rhoSequence,
      (normMatrixCoronaUnitaryEquiv X).symm.injective.comp
        ((nonUnitalStarAlgHomUnitaryMap_injective he).comp hrho)⟩
  exact (isCDEOperatorMF_iff_isOperatorMF G).mpr hop

/-- The corresponding implication to the internal group-theoretic MF
predicate. -/
theorem HasMFEmbedding.isOperatorMF
    {G : Type u} [Group G] [Countable G]
    {A : Type v} [CStarAlgebra A]
    (hA : HasMFEmbedding A)
    (rho : G →* unitary A) (hrho : Function.Injective rho) :
    IsOperatorMF G :=
  (isCDEOperatorMF_iff_isOperatorMF G).mp
    (hA.isCDEOperatorMF rho hrho)

/-- A group embeds in the unitary group of an algebra having the bare MF
embedding property.  This auxiliary group predicate deliberately does not
call the ambient algebra MF, because the ambient algebra need not be
separable. -/
def HasMFAlgebraUnitaryEmbedding (G : Type u) [Group G] : Prop :=
  ∃ (A : Type) (inst : CStarAlgebra A),
    letI : CStarAlgebra A := inst
    HasMFEmbedding A ∧
      ∃ rho : G →* unitary A, Function.Injective rho

/-- The literal CDE corona embedding gives an embedding into the unitary
group of an algebra having the bare MF embedding property. -/
theorem IsCDEOperatorMF.hasMFAlgebraUnitaryEmbedding
    {G : Type u} [Group G] [Countable G]
    (h : IsCDEOperatorMF G) : HasMFAlgebraUnitaryEmbedding G := by
  rcases h with ⟨d, hd, hmono, rho, hrho⟩
  let X : ℕ → FiniteModel := fun n ↦ naturalFiniteModel (d n)
  let hne : ∀ n, Nonempty (X n) := fun n ↦
    Fintype.card_pos_iff.mp (by simpa [X] using hd n)
  letI : ∀ n, Nonempty (X n) := hne
  refine ⟨NormMatrixCStarCorona (fun n ↦ X n), inferInstance, ?_⟩
  exact ⟨normMatrixCStarCorona_hasMFEmbedding X hne (by simpa [X] using hd)
    (by simpa [X] using hmono), rho, hrho⟩

/-- An embedding into the unitary group of an algebra with a bare MF
embedding composes, using the corner-complement correction above, to give
the literal CDE group embedding. -/
theorem HasMFAlgebraUnitaryEmbedding.isCDEOperatorMF
    {G : Type u} [Group G] [Countable G]
    (h : HasMFAlgebraUnitaryEmbedding G) : IsCDEOperatorMF G := by
  rcases h with ⟨A, inst, hA, rho, hrho⟩
  letI : CStarAlgebra A := inst
  exact hA.isCDEOperatorMF rho hrho

/-- For countable groups, unitary embeddability into an algebra with the bare
MF embedding property is equivalent to the group-theoretic MF property. -/
theorem hasMFAlgebraUnitaryEmbedding_iff_isOperatorMF
    (G : Type u) [Group G] [Countable G] :
    HasMFAlgebraUnitaryEmbedding G ↔ IsOperatorMF G := by
  rw [← isCDEOperatorMF_iff_isOperatorMF]
  exact ⟨HasMFAlgebraUnitaryEmbedding.isCDEOperatorMF,
    IsCDEOperatorMF.hasMFAlgebraUnitaryEmbedding⟩

end GroupApproximation
