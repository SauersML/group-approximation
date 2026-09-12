import GroupApproximation.Analysis.CStarProductCorona

/-!
# Functoriality of the reduced product

A family of `*`-homomorphisms `g m : M m → N m` acts coordinatewise on bounded
sequences, and — because a `*`-homomorphism of C-star algebras is contractive —
carries null sequences to null sequences.  So it descends to the reduced
products.  `coronaMap` is that descent.

The reduced product is a quotient by the null ideal, so the descent is
`Ideal.Quotient.lift`; the first four `*`-algebra clauses come free with the
ring homomorphism it produces, and only the adjoint and the scalars have to be
checked, which surjectivity of the quotient map reduces to the bounded level.

This is the bridge the gluing argument needs: the two legs of a symmetric
double are homomorphisms into `∏_t 𝒟 / ⨁_t 𝒟`, the representations they lift
are homomorphisms into `B(H)`, and `coronaMap` at the constant family
`g _ := q` is what carries the first picture to the second.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology PolarLiftingGeneralCStar

noncomputable section

universe u

section CoronaMap

variable {M N : ℕ → Type u}
  [∀ m, CStarAlgebra (M m)] [∀ m, Nontrivial (M m)]
  [∀ m, CStarAlgebra (N m)] [∀ m, Nontrivial (N m)]
variable (g : ∀ m, M m →⋆ₐ[ℂ] N m) (l : Filter ℕ)

/-- Coordinatewise application of a family of `*`-homomorphisms to a bounded
sequence.  Boundedness survives because each `g m` is contractive. -/
def boundedMap : BoundedCStarSequence M →⋆ₐ[ℂ] BoundedCStarSequence N where
  toFun x := ⟨fun m ↦ g m (x m), memℓp_infty ⟨‖x‖, by
    rintro _ ⟨m, rfl⟩
    exact (NonUnitalStarAlgHom.norm_apply_le (g m) (x m)).trans
      (boundedCStarSequence_coord_norm_le M x m)⟩⟩
  map_one' := by apply lp.ext; funext m; exact map_one (g m)
  map_mul' _ _ := by apply lp.ext; funext m; exact map_mul (g m) _ _
  map_zero' := by apply lp.ext; funext m; exact map_zero (g m)
  map_add' _ _ := by apply lp.ext; funext m; exact map_add (g m) _ _
  commutes' _ := by apply lp.ext; funext m; exact (g m).commutes _
  map_star' _ := by apply lp.ext; funext m; exact map_star (g m) _

@[simp] theorem boundedMap_apply (x : BoundedCStarSequence M) (m : ℕ) :
    boundedMap g x m = g m (x m) := rfl

/-- Coordinatewise `*`-homomorphisms carry null sequences to null sequences. -/
theorem isNull_boundedMap {x : BoundedCStarSequence M}
    (h : IsNullCStarSequence M l x) :
    IsNullCStarSequence N l (boundedMap g x) := by
  refine squeeze_zero (fun m ↦ norm_nonneg _) (fun m ↦ ?_) h
  exact NonUnitalStarAlgHom.norm_apply_le (g m) (x m)

/-- Coordinatewise application of a faithful family is faithful. -/
theorem boundedMap_injective (hg : ∀ m, Function.Injective (g m)) :
    Function.Injective (boundedMap g) := by
  intro x y h
  apply lp.ext
  funext m
  exact hg m (congrArg (fun z : BoundedCStarSequence N ↦ z m) h)

/-- The null ideal lies in the kernel of the composite into the target reduced
product, which is what lets the descent exist. -/
theorem coronaMap_kernel (x : BoundedCStarSequence M)
    (hx : x ∈ nullCStarSequenceIdeal M l) :
    cStarProductCoronaQuotient N l (boundedMap g x) = 0 :=
  (cStarProductCoronaQuotient_eq_zero_iff N l _).mpr
    (isNull_boundedMap g l hx)

/-- The descent, as a ring homomorphism. -/
def coronaMapRingHom : CStarProductCorona M l →+* CStarProductCorona N l :=
  Ideal.Quotient.lift (nullCStarSequenceIdeal M l)
    (((cStarProductCoronaQuotient N l).comp (boundedMap g)).toAlgHom.toRingHom)
    (coronaMap_kernel g l)

@[simp] theorem coronaMapRingHom_mk (a : BoundedCStarSequence M) :
    coronaMapRingHom g l (cStarProductCoronaQuotient M l a) =
      cStarProductCoronaQuotient N l (boundedMap g a) :=
  Ideal.Quotient.lift_mk _ _ _

/-- **Functoriality of the reduced product.**  A coordinatewise family of
`*`-homomorphisms descends to a `*`-homomorphism of reduced products. -/
def coronaMap : CStarProductCorona M l →⋆ₐ[ℂ] CStarProductCorona N l where
  toFun := coronaMapRingHom g l
  map_one' := map_one (coronaMapRingHom g l)
  map_mul' := map_mul (coronaMapRingHom g l)
  map_zero' := map_zero (coronaMapRingHom g l)
  map_add' := map_add (coronaMapRingHom g l)
  commutes' r := by
    -- `.commutes` on a `StarAlgHom` is stated through its `AlgHom` coercion, so
    -- its pattern does not appear in a goal written with the `StarAlgHom`
    -- coercion; `AlgHomClass.commutes` applies to the hom itself.
    have h := coronaMapRingHom_mk g l (algebraMap ℂ (BoundedCStarSequence M) r)
    have hM : cStarProductCoronaQuotient M l
        (algebraMap ℂ (BoundedCStarSequence M) r)
        = algebraMap ℂ (CStarProductCorona M l) r :=
      AlgHomClass.commutes (cStarProductCoronaQuotient M l) r
    have hB : boundedMap g (algebraMap ℂ (BoundedCStarSequence M) r)
        = algebraMap ℂ (BoundedCStarSequence N) r :=
      AlgHomClass.commutes (boundedMap g) r
    have hN : cStarProductCoronaQuotient N l
        (algebraMap ℂ (BoundedCStarSequence N) r)
        = algebraMap ℂ (CStarProductCorona N l) r :=
      AlgHomClass.commutes (cStarProductCoronaQuotient N l) r
    rw [hM, hB, hN] at h
    exact h
  map_star' x := by
    obtain ⟨a, rfl⟩ := cStarProductCoronaQuotient_surjective M l x
    rw [← map_star (cStarProductCoronaQuotient M l) a, coronaMapRingHom_mk,
      coronaMapRingHom_mk, map_star (boundedMap g) a,
      map_star (cStarProductCoronaQuotient N l) _]

@[simp] theorem coronaMap_mk (a : BoundedCStarSequence M) :
    coronaMap g l (cStarProductCoronaQuotient M l a) =
      cStarProductCoronaQuotient N l (boundedMap g a) :=
  coronaMapRingHom_mk g l a

end CoronaMap

/-! ## The constant embedding -/

section Const

variable {E : Type u} [CStarAlgebra E] [Nontrivial E] (l : Filter ℕ) [l.NeBot]

/-- The constant sequence at `T`, as a bounded sequence. -/
def constSeq (T : E) : BoundedCStarSequence (fun _ : ℕ ↦ E) :=
  ⟨fun _ ↦ T, memℓp_infty ⟨‖T‖, by rintro _ ⟨m, rfl⟩; exact le_rfl⟩⟩

omit [Nontrivial E] in
@[simp] theorem constSeq_apply (T : E) (m : ℕ) : constSeq T m = T := rfl

/-- **The constant embedding of `E` in its own reduced product.**  It is a
`*`-homomorphism because the operations of the product are coordinatewise. -/
def constCorona : E →⋆ₐ[ℂ] CStarProductCorona (fun _ : ℕ ↦ E) l :=
  (cStarProductCoronaQuotient (fun _ : ℕ ↦ E) l).comp
    ({ toFun := constSeq
       map_one' := by apply lp.ext; funext m; rfl
       map_mul' _ _ := by apply lp.ext; funext m; rfl
       map_zero' := by apply lp.ext; funext m; rfl
       map_add' _ _ := by apply lp.ext; funext m; rfl
       commutes' _ := by apply lp.ext; funext m; rfl
       map_star' _ := by apply lp.ext; funext m; rfl } :
      E →⋆ₐ[ℂ] BoundedCStarSequence (fun _ : ℕ ↦ E))

/-- **The constant embedding is faithful.**  A constant sequence is null along
a nontrivial filter only when the constant is zero. -/
theorem constCorona_injective : Function.Injective (constCorona (E := E) l) := by
  intro S T hST
  have hzero : constCorona (E := E) l (S - T) = 0 := by
    rw [map_sub, hST, sub_self]
  have hnull : IsNullCStarSequence (fun _ : ℕ ↦ E) l (constSeq (S - T)) :=
    (cStarProductCoronaQuotient_eq_zero_iff (fun _ : ℕ ↦ E) l _).mp hzero
  have hconst : Tendsto (fun _ : ℕ ↦ ‖S - T‖) l (𝓝 0) := hnull
  have : ‖S - T‖ = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

end Const

end

end ShulmanFill
end GroupApproximation
