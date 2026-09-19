import GroupApproximation.Manuscript.MFRecognition.TensorSynchronization

/-!
# `lem:tensor-sync`: the three printed sentences the main development bypasses

`TensorSynchronization.lean` proves `lem:tensor-sync`, but three printed
sentences of its proof are reached there by a different route and so have no
declaration of their own.  This module states and proves them, so that the
sentence census carries a declaration for every printed sentence of the lemma.
Nothing here is used by the main development; it is a leaf.

## The restriction of the regular representation

> The restriction of `L_n` to a subgroup of `E_n` is unitarily equivalent to
> the direct sum of as many copies of the left regular representation of that
> subgroup as it has right cosets.

`TensorSynchronizationCore.exists_leftRegular_conjugator_of_ker_eq` produces
the conjugating permutation `W_n` from a right-coset transversal, so the
decomposition is present in that construction but not as a statement.  Here it
is the statement: a right transversal `d` of `K` in `E` makes
`(k,t) ↦ k · d t` a bijection `K × T ≃ E`, and conjugating by it turns left
translation by `s ∈ K` into `L_K(s) ⊕ ⋯ ⊕ L_K(s)`, one summand for each
element of `T`.  The count is `card E = card K * card T`, so `T` indexes the
right cosets exactly as printed.

## The corner complement

> Let `ι` be an injective `*`-homomorphism of `A` into a norm matrix corona
> and put `p = ι(1)`.  The element `W̃ = ι(W) + (1−p)` is a unitary of the full
> corona and implements the required covariance on `ι(A)`, so it is the
> required conjugator.

The main development takes `ι` unital — that is what
`HNNPermanenceInputs.unitalCoronaEmbedding` supplies — so there `p = 1` and the
correction term vanishes.  Over the possibly non-unital embedding that
`HasMFEmbedding` actually provides, the printed correction is exactly the
repository's `nonUnitalStarAlgHomUnitaryMap`, and the two printed claims about
it — that `p` is a projection and that `W̃` is a unitary implementing the
covariance on the image of `ι` — are proved below.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace TensorSynchronization

open GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationAssembly

noncomputable section

universe u v

/-! ## The right-transversal decomposition of the regular representation -/

/-- The decomposition `K × T ≃ E` attached to a right transversal `d` of the
subgroup `K`: the map `(k,t) ↦ k · d t`.  Its bijectivity is precisely the
statement that `d` picks one representative from each right coset of `K`. -/
def transversalProdEquiv {E : Type u} [Group E] (K : Subgroup E) {T : Type v}
    (d : T → E) (hd : Function.Bijective fun p : K × T ↦ (p.1 : E) * d p.2) :
    K × T ≃ E :=
  Equiv.ofBijective _ hd

/-- Left translation by an element of `K` moves the `K`-coordinate of the
transversal decomposition and fixes the transversal coordinate.  This is the
pointwise form of the printed equivalence. -/
theorem transversalProdEquiv_mulLeft {E : Type u} [Group E] (K : Subgroup E)
    {T : Type v} (d : T → E)
    (hd : Function.Bijective fun p : K × T ↦ (p.1 : E) * d p.2)
    (s : K) (p : K × T) :
    transversalProdEquiv K d hd
        (((Equiv.mulLeft s).prodCongr (Equiv.refl T)) p) =
      Equiv.mulLeft (s : E) (transversalProdEquiv K d hd p) := by
  have hcoe : ((s * p.1 : K) : E) = (s : E) * (p.1 : E) := rfl
  show ((s * p.1 : K) : E) * d p.2 = (s : E) * ((p.1 : E) * d p.2)
  rw [hcoe, mul_assoc]

/-- **The printed reason.**  "The restriction of `L_n` to a subgroup of `E_n`
is unitarily equivalent to the direct sum of as many copies of the left
regular representation of that subgroup as it has right cosets."

Conjugating the left regular permutation representation of `E` at an element
of `K` by the transversal decomposition gives the left regular permutation
representation of `K` acting on the `K`-coordinate alone, i.e. one copy of
`L_K` for each element of the transversal `T`. -/
theorem leftRegularPermutationHom_restrict_conj {E : Type u} [Group E]
    (K : Subgroup E) {T : Type v} (d : T → E)
    (hd : Function.Bijective fun p : K × T ↦ (p.1 : E) * d p.2) (s : K) :
    (transversalProdEquiv K d hd).symm.trans
        ((((leftRegularPermutationHom K) s).prodCongr (Equiv.refl T)).trans
          (transversalProdEquiv K d hd)) =
      leftRegularPermutationHom E (s : E) := by
  apply Equiv.ext
  intro g
  obtain ⟨p, rfl⟩ := hd.surjective g
  show transversalProdEquiv K d hd
      (((Equiv.mulLeft s).prodCongr (Equiv.refl T))
        ((transversalProdEquiv K d hd).symm
          (transversalProdEquiv K d hd p))) =
    Equiv.mulLeft (s : E) (transversalProdEquiv K d hd p)
  rw [Equiv.symm_apply_apply]
  exact transversalProdEquiv_mulLeft K d hd s p

/-- "As many copies as it has right cosets": the transversal index set has
exactly the index of `K` as its cardinality. -/
theorem card_eq_card_mul_card_transversal {E : Type u} [Group E]
    (K : Subgroup E) {T : Type v} (d : T → E)
    (hd : Function.Bijective fun p : K × T ↦ (p.1 : E) * d p.2)
    [Fintype E] [Fintype K] [Fintype T] :
    Fintype.card E = Fintype.card K * Fintype.card T := by
  rw [← Fintype.card_prod]
  exact (Fintype.card_congr (transversalProdEquiv K d hd)).symm

/-! ## The corner complement `W̃ = ι(W) + (1 − p)` -/

/-- "Put `p = ι(1)`": the image of the unit under a possibly non-unital star
homomorphism is a projection. -/
theorem cornerProjection {A : Type u} {C : Type v} [CStarAlgebra A]
    [CStarAlgebra C] (e : A →⋆ₙₐ[ℂ] C) :
    star (e (1 : A)) = e (1 : A) ∧ e (1 : A) * e (1 : A) = e (1 : A) := by
  constructor
  · rw [← map_star, star_one]
  · rw [← map_mul, one_mul]

/-- "The element `W̃ = ι(W) + (1−p)` is a unitary of the full corona." -/
theorem cornerComplement_mem_unitary {A : Type u} {C : Type v} [CStarAlgebra A]
    [CStarAlgebra C] (e : A →⋆ₙₐ[ℂ] C) (W : unitary A) :
    e (W : A) + (1 - e (1 : A)) ∈ unitary C :=
  (nonUnitalStarAlgHomUnitaryMap e W).property

/-- "... and implements the required covariance on `ι(A)`, so it is the
required conjugator."

Conjugation by `W̃` agrees, on the image of `e`, with the image of conjugation
by `W`; applied to `e (ρ(s))` and the covariance `W ρ(s) W* = ρ(θ(s))` in `A`
this is exactly the hypothesis `thm:hnn-permanence` asks for. -/
theorem cornerComplement_conjugation {A : Type u} {C : Type v} [CStarAlgebra A]
    [CStarAlgebra C] (e : A →⋆ₙₐ[ℂ] C) (W : unitary A) (x : A) :
    ((nonUnitalStarAlgHomUnitaryMap e W : unitary C) : C) * e x *
        star ((nonUnitalStarAlgHomUnitaryMap e W : unitary C) : C) =
      e ((W : A) * x * star (W : A)) := by
  have hcoe : ((nonUnitalStarAlgHomUnitaryMap e W : unitary C) : C)
      = e (W : A) + (1 - e (1 : A)) := rfl
  have hp_star : star (e (1 : A)) = e (1 : A) := (cornerProjection e).1
  have hxp : e x * e (1 : A) = e x := by
    rw [← map_mul, mul_one]
  have hpx : e (1 : A) * e x = e x := by
    rw [← map_mul, one_mul]
  have hwstar : star (e (W : A)) = e (star (W : A)) := (map_star e (W : A)).symm
  have h1 : (e (W : A) + (1 - e (1 : A))) * e x = e (W : A) * e x := by
    have hexp : (e (W : A) + (1 - e (1 : A))) * e x
        = e (W : A) * e x + e x - e (1 : A) * e x := by noncomm_ring
    rw [hexp, hpx]
    abel
  have h2 : e (W : A) * e x * (e (star (W : A)) + (1 - e (1 : A)))
      = e (W : A) * e x * e (star (W : A)) := by
    have hexp : e (W : A) * e x * (e (star (W : A)) + (1 - e (1 : A)))
        = e (W : A) * e x * e (star (W : A)) + e (W : A) * e x -
          e (W : A) * e x * e (1 : A) := by noncomm_ring
    have h3 : e (W : A) * e x * e (1 : A) = e (W : A) * e x := by
      rw [mul_assoc, hxp]
    rw [hexp, h3]
    abel
  calc
    ((nonUnitalStarAlgHomUnitaryMap e W : unitary C) : C) * e x *
        star ((nonUnitalStarAlgHomUnitaryMap e W : unitary C) : C)
        = (e (W : A) + (1 - e (1 : A))) * e x *
            (e (star (W : A)) + (1 - e (1 : A))) := by
          rw [hcoe, star_add, star_sub, star_one, hp_star, hwstar]
    _ = e (W : A) * e x * (e (star (W : A)) + (1 - e (1 : A))) := by rw [h1]
    _ = e (W : A) * e x * e (star (W : A)) := h2
    _ = e ((W : A) * x * star (W : A)) := by
          rw [← map_mul e (W : A) x, ← map_mul e ((W : A) * x) (star (W : A))]

end

end TensorSynchronization
end MFRecognition
end Manuscript
end GroupApproximation
