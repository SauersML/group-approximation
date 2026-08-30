import GroupApproximation.Analysis.VoiculescuBlockIsometry

/-!
# (V4) A representation restricted to an invariant block

The assembly runs the intertwining step on each block of the source separately,
and the intertwining step wants a genuine `⋆`-homomorphism on each block.  This
module builds it: a closed subspace invariant under all of `ρ(C)` carries the
restriction of `ρ` as a `⋆`-homomorphism into the operators on that subspace.

## Where the `⋆` comes from

Invariance alone gives a homomorphism of algebras; the `⋆` needs the block to be
*reducing*, that is invariant under the adjoints as well.  It is, and for free:
`C` is `⋆`-closed and the block is asked to be invariant under `ρ(a)` for every
`a`, so it is invariant under `ρ(a⋆) = ρ(a)⋆`.  That is the only place the
hypothesis is used in that strength, and it is why the datum quantifies over all
of `C` rather than over a generating set.

Concretely `blockRestrict_star` is proved through `eq_adjoint_iff`: on the block
the inner product is the ambient one (`Submodule.coe_inner`), so the identity to
check is the ambient `⟪T⋆x, y⟫ = ⟪x, Ty⟫`.

`blockRestrict_congr` is what carries the algebraic laws across: the restriction
depends on a proof of invariance as well as on the operator, so equal operators
give equal restrictions only after the proofs are discharged by irrelevance, and
rewriting under the dependent argument needs that lemma rather than `rw`.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace

noncomputable section

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] {L : Submodule ℂ K} [CompleteSpace ↥L]

/-! ## The restriction of one operator -/

/-- An operator leaving a subspace invariant, restricted to it. -/
def blockRestrict (T : K →L[ℂ] K) (h : ∀ x ∈ L, T x ∈ L) : ↥L →L[ℂ] ↥L :=
  T.restrict h

omit [CompleteSpace K] [CompleteSpace ↥L] in
@[simp] theorem coe_blockRestrict (T : K →L[ℂ] K) (h : ∀ x ∈ L, T x ∈ L)
    (x : ↥L) : ((blockRestrict T h x : ↥L) : K) = T (x : K) := rfl

omit [CompleteSpace K] [CompleteSpace ↥L] in
/-- Equal operators have equal restrictions; the invariance proofs are
irrelevant.  This is what lets the algebraic laws be transported. -/
theorem blockRestrict_congr {S T : K →L[ℂ] K} (hS : ∀ x ∈ L, S x ∈ L)
    (hT : ∀ x ∈ L, T x ∈ L) (hST : S = T) :
    blockRestrict S hS = blockRestrict T hT := by
  subst hST
  rfl

omit [CompleteSpace K] [CompleteSpace ↥L] in
theorem blockRestrict_one (h : ∀ x ∈ L, (1 : K →L[ℂ] K) x ∈ L) :
    blockRestrict (1 : K →L[ℂ] K) h = 1 := by
  refine ContinuousLinearMap.ext fun x ↦ Subtype.ext ?_
  rw [coe_blockRestrict]
  rfl

omit [CompleteSpace K] [CompleteSpace ↥L] in
theorem blockRestrict_mul (S T : K →L[ℂ] K) (hS : ∀ x ∈ L, S x ∈ L)
    (hT : ∀ x ∈ L, T x ∈ L) (hST : ∀ x ∈ L, (S * T) x ∈ L) :
    blockRestrict (S * T) hST = blockRestrict S hS * blockRestrict T hT := by
  refine ContinuousLinearMap.ext fun x ↦ Subtype.ext ?_
  rw [coe_blockRestrict]
  rfl

omit [CompleteSpace K] [CompleteSpace ↥L] in
theorem blockRestrict_add (S T : K →L[ℂ] K) (hS : ∀ x ∈ L, S x ∈ L)
    (hT : ∀ x ∈ L, T x ∈ L) (hST : ∀ x ∈ L, (S + T) x ∈ L) :
    blockRestrict (S + T) hST = blockRestrict S hS + blockRestrict T hT := by
  refine ContinuousLinearMap.ext fun x ↦ Subtype.ext ?_
  rw [coe_blockRestrict]
  rfl

/-- **The restriction respects the star**, which is where the block has to be
reducing rather than merely invariant. -/
theorem blockRestrict_star (T : K →L[ℂ] K) (hT : ∀ x ∈ L, T x ∈ L)
    (hTs : ∀ x ∈ L, (star T) x ∈ L) :
    blockRestrict (star T) hTs = star (blockRestrict T hT) := by
  have hgoal : star (blockRestrict T hT)
      = ContinuousLinearMap.adjoint (blockRestrict T hT) :=
    ContinuousLinearMap.star_eq_adjoint _
  rw [hgoal]
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y ↦ ?_
  rw [Submodule.coe_inner, Submodule.coe_inner, coe_blockRestrict,
    coe_blockRestrict, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

/-! ## The block representation -/

variable {C : Type} [CStarAlgebra C]

variable (L) in
/-- **A representation restricted to an invariant block.** -/
def blockRep (rho : C →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hL : ∀ (a : C) (x : K), x ∈ L → rho a x ∈ L) : C →⋆ₐ[ℂ] (↥L →L[ℂ] ↥L) where
  toFun a := blockRestrict (rho a) (hL a)
  map_one' := by
    have h1 : ∀ x ∈ L, (1 : K →L[ℂ] K) x ∈ L := by
      intro x hx
      rw [← map_one rho]
      exact hL 1 x hx
    rw [blockRestrict_congr (hL 1) h1 (map_one rho), blockRestrict_one h1]
  map_mul' a b := by
    have h1 : ∀ x ∈ L, (rho a * rho b) x ∈ L := by
      intro x hx
      rw [← map_mul rho]
      exact hL (a * b) x hx
    rw [blockRestrict_congr (hL (a * b)) h1 (map_mul rho a b),
      blockRestrict_mul (rho a) (rho b) (hL a) (hL b)]
  map_zero' := by
    refine ContinuousLinearMap.ext fun x ↦ Subtype.ext ?_
    rw [coe_blockRestrict, map_zero]
    rfl
  map_add' a b := by
    have h1 : ∀ x ∈ L, (rho a + rho b) x ∈ L := by
      intro x hx
      rw [← map_add rho]
      exact hL (a + b) x hx
    rw [blockRestrict_congr (hL (a + b)) h1 (map_add rho a b),
      blockRestrict_add (rho a) (rho b) (hL a) (hL b)]
  commutes' z := by
    refine ContinuousLinearMap.ext fun x ↦ Subtype.ext ?_
    rw [coe_blockRestrict, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one]
    rfl
  map_star' a := by
    have h1 : ∀ x ∈ L, (star (rho a)) x ∈ L := by
      intro x hx
      rw [← map_star rho a]
      exact hL (star a) x hx
    rw [blockRestrict_congr (hL (star a)) h1 (map_star rho a),
      blockRestrict_star (rho a) (hL a)]

@[simp] theorem coe_blockRep_apply (rho : C →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hL : ∀ (a : C) (x : K), x ∈ L → rho a x ∈ L) (a : C) (x : ↥L) :
    ((blockRep L rho hL a x : ↥L) : K) = rho a (x : K) := rfl

/-- **The block representation intertwines with the inclusion**, which is the
form the assembly consumes: on the block, `ρ` and its restriction agree. -/
theorem blockRep_intertwines (rho : C →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hL : ∀ (a : C) (x : K), x ∈ L → rho a x ∈ L) (a : C) (x : ↥L) :
    L.subtypeL (blockRep L rho hL a x) = rho a (L.subtypeL x) := rfl

end

end ShulmanFill
end GroupApproximation
