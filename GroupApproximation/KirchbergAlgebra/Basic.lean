import GroupApproximation.Analysis.CStarSimple
import GroupApproximation.Analysis.CStarNuclearProduct
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra

/-!
# Kirchberg algebras

The textbook notions behind the Kirchberg disjunct of STW Problem L.

* `IsHereditaryCStarSubalgebra H`: `H` is a closed `⋆`-subalgebra with `b a b' ∈ H` for
  `b, b' ∈ H` and `a ∈ A`. Murphy, *C⋆-algebras and operator theory*, Theorem 3.2.2, shows that
  this is equivalent to the order form `0 ≤ a ≤ b ∈ H ⇒ a ∈ H`.
* `IsInfiniteProjection p`: `p` is a projection that is Murray–von Neumann equivalent to a proper
  subprojection, `v⋆v = p`, `vv⋆ ≤ p` and `vv⋆ ≠ p` (Blackadar, *Operator algebras*, III.1.3.1).
  For projections `q ≤ p` means `q p = q`.
* `IsPurelyInfiniteSimple A`: `A` is nonzero and simple, and every nonzero hereditary
  C⋆-subalgebra contains an infinite projection (Cuntz; Rørdam, *Classification of nuclear
  C⋆-algebras*, Definition 4.1.2).
* `IsKirchbergAlgebra A`: `A` is separable, nuclear, simple and purely infinite (Rørdam, loc. cit.,
  Chapter 8). Simplicity is `IsSimpleCStar` (closed two-sided ideals) and nuclearity is the
  completely positive approximation property `IsNuclearCStarAlgebra` of `CStarExactness`
  (Brown–Ozawa, *C⋆-algebras and finite-dimensional approximations*, §2.3). The carrier is a
  unital C⋆-algebra.

The API transports all four notions along `⋆`-algebra isomorphisms, shows that `ℂ` is not purely
infinite, and proves the easy half of Cuntz's criterion: if `x a y = 1` is solvable for every
`a ≠ 0`, then `A` is simple.
-/

namespace GroupApproximation
namespace KirchbergAlgebra

open CStarExactness

universe u v

section Defs

variable {A : Type u} [CStarAlgebra A]

/-- A hereditary C⋆-subalgebra: a closed `⋆`-subalgebra `H` with `b a b' ∈ H` for `b, b' ∈ H`
and `a ∈ A` (Murphy, Theorem 3.2.2). -/
def IsHereditaryCStarSubalgebra (H : NonUnitalStarSubalgebra ℂ A) : Prop :=
  IsClosed (H : Set A) ∧ ∀ b ∈ H, ∀ a : A, ∀ b' ∈ H, b * a * b' ∈ H

/-- An infinite projection: `p` is a projection with `v⋆v = p`, `vv⋆ ≤ p` and `vv⋆ ≠ p` for some
`v` (Blackadar, III.1.3.1). -/
def IsInfiniteProjection (p : A) : Prop :=
  IsStarProjection p ∧ ∃ v : A, star v * v = p ∧ v * star v * p = v * star v ∧ v * star v ≠ p

variable (A)

/-- A purely infinite simple C⋆-algebra: nonzero, simple, and every nonzero hereditary
C⋆-subalgebra contains an infinite projection (Rørdam, Definition 4.1.2). -/
def IsPurelyInfiniteSimple : Prop :=
  Nontrivial A ∧ IsSimpleCStar A ∧ ∀ H : NonUnitalStarSubalgebra ℂ A,
    IsHereditaryCStarSubalgebra H → H ≠ ⊥ → ∃ p ∈ H, IsInfiniteProjection p

/-- A (unital) Kirchberg algebra: a separable, nuclear, purely infinite simple C⋆-algebra. -/
def IsKirchbergAlgebra : Prop :=
  TopologicalSpace.SeparableSpace A ∧ IsNuclearCStarAlgebra A ∧ IsPurelyInfiniteSimple A

end Defs

section API

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

/-- A non-unitary isometry makes `1` an infinite projection. -/
theorem isInfiniteProjection_one_of_isometry {v : A} (hv : star v * v = 1)
    (hv' : v * star v ≠ 1) : IsInfiniteProjection (1 : A) :=
  ⟨IsStarProjection.one A, v, hv, mul_one _, hv'⟩

/-- An infinite projection gives a non-normal element; commutative algebras have none. -/
theorem IsInfiniteProjection.exists_star_mul_ne {p : A} (hp : IsInfiniteProjection p) :
    ∃ v : A, star v * v ≠ v * star v := by
  obtain ⟨-, v, hv, -, hne⟩ := hp
  exact ⟨v, fun h => hne (h.symm.trans hv)⟩

theorem IsInfiniteProjection.map (e : A ≃⋆ₐ[ℂ] B) {p : A} (hp : IsInfiniteProjection p) :
    IsInfiniteProjection (e p) := by
  obtain ⟨hproj, v, hv, hle, hne⟩ := hp
  have hproj' : IsStarProjection (e p) :=
    { isIdempotentElem := by
        show e p * e p = e p
        rw [← map_mul, hproj.isIdempotentElem.eq]
      isSelfAdjoint := by
        show star (e p) = e p
        rw [← map_star, hproj.isSelfAdjoint.star_eq] }
  refine ⟨hproj', e v, ?_, ?_, ?_⟩
  · rw [← map_star, ← map_mul, hv]
  · rw [← map_star, ← map_mul, ← map_mul, hle]
  · intro h
    apply hne
    apply EquivLike.injective e
    rw [map_mul, map_star, h]

theorem IsHereditaryCStarSubalgebra.comap (e : A ≃⋆ₐ[ℂ] B) {H : NonUnitalStarSubalgebra ℂ B}
    (hH : IsHereditaryCStarSubalgebra H) :
    IsHereditaryCStarSubalgebra (NonUnitalStarSubalgebra.comap e H) := by
  constructor
  · exact hH.1.preimage (StarAlgEquiv.isometry e).continuous
  · intro b hb a b' hb'
    rw [NonUnitalStarSubalgebra.mem_comap] at hb hb' ⊢
    rw [map_mul, map_mul]
    exact hH.2 _ hb _ _ hb'

theorem IsPurelyInfiniteSimple.of_starAlgEquiv (e : A ≃⋆ₐ[ℂ] B)
    (h : IsPurelyInfiniteSimple A) : IsPurelyInfiniteSimple B := by
  obtain ⟨hnt, hs, hpi⟩ := h
  refine ⟨?_, hs.of_starAlgEquiv e, fun H hH hne => ?_⟩
  · haveI := hnt
    exact (EquivLike.injective e).nontrivial
  have hne' : NonUnitalStarSubalgebra.comap e H ≠ ⊥ := by
    intro hbot
    apply hne
    refine eq_bot_iff.2 fun x hx => NonUnitalStarAlgebra.mem_bot.2 ?_
    have hx' : e.symm x ∈ NonUnitalStarSubalgebra.comap e H := by
      rw [NonUnitalStarSubalgebra.mem_comap, StarAlgEquiv.apply_symm_apply]
      exact hx
    rw [hbot, NonUnitalStarAlgebra.mem_bot] at hx'
    rw [← StarAlgEquiv.apply_symm_apply e x, hx', map_zero]
  obtain ⟨p, hp, hinf⟩ := hpi (NonUnitalStarSubalgebra.comap e H) (hH.comap e) hne'
  exact ⟨e p, (NonUnitalStarSubalgebra.mem_comap _ _ _).1 hp, hinf.map e⟩

theorem IsKirchbergAlgebra.of_starAlgEquiv (e : A ≃⋆ₐ[ℂ] B) (h : IsKirchbergAlgebra A) :
    IsKirchbergAlgebra B := by
  obtain ⟨hsep, hnuc, hpi⟩ := h
  refine ⟨?_, IsNuclearCStarAlgebra.of_starAlgEquiv e.symm hnuc, hpi.of_starAlgEquiv e⟩
  haveI := hsep
  exact (EquivLike.surjective e).denseRange.separableSpace (StarAlgEquiv.isometry e).continuous

/-- Model test: `ℂ` is not purely infinite, since it has no infinite projection. -/
theorem not_isPurelyInfiniteSimple_complex : ¬ IsPurelyInfiniteSimple ℂ := by
  rintro ⟨-, -, h⟩
  have hclosed : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ ℂ) : Set ℂ) := by
    rw [NonUnitalStarAlgebra.coe_top]
    exact isClosed_univ
  have hne : (⊤ : NonUnitalStarSubalgebra ℂ ℂ) ≠ ⊥ := by
    intro htop
    have h1 : (1 : ℂ) ∈ (⊤ : NonUnitalStarSubalgebra ℂ ℂ) := NonUnitalStarAlgebra.mem_top
    rw [htop, NonUnitalStarAlgebra.mem_bot] at h1
    exact one_ne_zero h1
  obtain ⟨p, -, hp⟩ := h ⊤ ⟨hclosed, fun _ _ _ _ _ => NonUnitalStarAlgebra.mem_top⟩ hne
  obtain ⟨-, v, hv, -, hne'⟩ := hp
  exact hne' (by rw [mul_comm]; exact hv)

/-- The easy half of Cuntz's criterion: if `x a y = 1` is solvable for every `a ≠ 0`, then every
nonzero closed two-sided ideal is everything. -/
theorem isSimpleCStar_of_forall_exists_mul_mul_eq_one
    (h : ∀ a : A, a ≠ 0 → ∃ x y : A, x * a * y = 1) : IsSimpleCStar A := by
  intro I hI _
  haveI := hI
  refine or_iff_not_imp_left.2 fun hbot => ?_
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff I).1 hbot
  obtain ⟨x, y, hxy⟩ := h a ha0
  have h1 : x * a * y ∈ I := Ideal.mul_mem_right y I (I.mul_mem_left x ha)
  rw [hxy] at h1
  rw [Ideal.eq_top_iff_one]
  exact h1

end API

end KirchbergAlgebra
end GroupApproximation
