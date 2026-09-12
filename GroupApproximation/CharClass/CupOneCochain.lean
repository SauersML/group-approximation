import GroupApproximation.CharClass.CupOneSign
import GroupApproximation.CharClass.SteenrodCupEdge

/-!
# The signed cup-1 product on singular cochains

`SteenrodCochain.cochainCupI` is already generic in the coefficient ring, but it
carries no signs, so over a ring in which `1 ≠ -1` it is not a chain homotopy.  This
file adds the sign of `CupOneSign.lean` to the two-point cuts, and records the one
cochain-level fact the coboundary formula needs beyond `SteenrodCochain.lean`: the
**signed** coboundary through a face.

## The signed coboundary through a face

`SteenrodCochain.faceVal_coboundary` reads `δα` on a face as the unsigned sum over
the vertices of that face, which is true only mod 2.  The honest statement is

```text
faceVal (a+1) (δα) τ A = ∑ c ∈ A, (-1)^(cutRank A c) * faceVal a α τ (A.erase c),
```

with `cutRank A c` the number of vertices of `A` below `c` — that is, the *position*
of `c` in `A`, which is exactly the index the alternating face sum uses.  The bridge
is `cutRank_orderEmbOfFin`: the rank of the `i`-th smallest element of `A` is `i`.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass

noncomputable section

/-! ## 1. The position of a vertex inside a face -/

theorem filter_univ_lt {N : ℕ} (x : Fin N) :
    Finset.univ.filter (fun c : Fin N => c < x) = Finset.Iio x := by
  ext c
  rw [Finset.mem_filter, Finset.mem_Iio]
  exact ⟨fun hc => hc.2, fun hc => ⟨Finset.mem_univ c, hc⟩⟩

/-- **The rank of the `i`-th smallest element of `A` is `i`.**  This is what makes the
alternating face sign of a face the `cutRank` of the deleted vertex. -/
theorem cutRank_orderEmbOfFin {N k : ℕ} (A : Finset (Fin N)) (h : A.card = k + 1)
    (i : Fin (k + 1)) : cutRank A (A.orderEmbOfFin h i) = i.val := by
  classical
  unfold cutRank
  have himg : A.filter (fun c => c < A.orderEmbOfFin h i)
      = (Finset.univ.filter (fun j : Fin (k + 1) => j < i)).image (A.orderEmbOfFin h) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hxA, hx⟩
      have hrange : x ∈ Set.range (A.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_coe.2 hxA
      obtain ⟨j, rfl⟩ := hrange
      exact ⟨j, (A.orderEmbOfFin h).strictMono.lt_iff_lt.1 hx, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨A.orderEmbOfFin_mem h j, (A.orderEmbOfFin h).strictMono hj⟩
  rw [himg, Finset.card_image_of_injective _ (A.orderEmbOfFin h).injective, filter_univ_lt,
    Fin.card_Iio]

/-! ## 2. The signed coboundary through a face -/

/-- **The coboundary through a face, with its signs.**  The generic replacement for
`SteenrodCochain.faceVal_coboundary`, which drops the signs with `neg_one_pow_zmod2`.
Both sides vanish when `A` has the wrong size. -/
theorem faceVal_coboundary_signed {K : Type} [CommRing K] {X : TopCat.{0}} (a n : ℕ)
    (α : singularCochainGroup K X a) (τ : singularSimplices X (n + 1))
    (A : Finset (Fin (n + 2))) :
    faceVal (a + 1) (cochainCoboundary K X a α) τ A
      = ∑ c ∈ A, (-1 : K) ^ cutRank A c * faceVal a α τ (A.erase c) := by
  classical
  by_cases h : A.card = a + 1 + 1
  · rw [faceVal_of_card (a + 1) (cochainCoboundary K X a α) τ h, cochainCoboundary_eval]
    have hterm : ∀ i : Fin (a + 2),
        (-1 : K) ^ (i : ℕ)
            * cochainEval a α (faceSimplex X a i (restrictSimplex (faceOfFinset A h) τ))
          = (-1 : K) ^ cutRank A (A.orderEmbOfFin h i)
              * faceVal a α τ (A.erase (A.orderEmbOfFin h i)) := by
      intro i
      have hcard : (A.erase (A.orderEmbOfFin h i)).card = a + 1 := by
        have := Finset.card_erase_of_mem (A.orderEmbOfFin_mem h i)
        omega
      have hsimp : faceSimplex X a i (restrictSimplex (faceOfFinset A h) τ)
          = restrictSimplex (faceOfFinset (A.erase (A.orderEmbOfFin h i)) hcard) τ := by
        rw [faceSimplex_eq_restrictSimplex, restrictSimplex_comp, delta_comp_faceOfFinset]
      rw [cutRank_orderEmbOfFin A h i, faceVal_of_card a α τ hcard, hsimp]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i)]
    refine Finset.sum_bij (fun (i : Fin (a + 2)) _ => A.orderEmbOfFin h i) ?_ ?_ ?_ ?_
    · intro i _
      exact A.orderEmbOfFin_mem h i
    · intro i₁ _ i₂ _ heq
      exact (A.orderEmbOfFin h).injective heq
    · intro c hc
      have hrange : c ∈ Set.range (A.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_coe.2 hc
      obtain ⟨i, hi⟩ := hrange
      exact ⟨i, Finset.mem_univ i, hi⟩
    · intro i _
      rfl
  · rw [faceVal_of_card_ne (cochainCoboundary K X a α) τ h]
    refine (Finset.sum_eq_zero ?_).symm
    intro c hc
    have hne : ¬ (A.erase c).card = a + 1 := by
      have hce := Finset.card_erase_of_mem hc
      have hpos : 1 ≤ A.card := Finset.card_pos.2 ⟨c, hc⟩
      omega
    rw [faceVal_of_card_ne α τ hne, mul_zero]

/-! ## 3. The signed cup-1 product -/

/-- **Steenrod's cup-1 product with signs.**  The same sum over two-point cuts as
`cochainCupI 1`, weighted by `cupOneSign`.  As there, the output degree is a free
parameter and the terms of the wrong bidegree vanish because `faceVal` does. -/
def cochainCupOne {K : Type} [CommRing K] {X : TopCat.{0}} (a b n : ℕ)
    (α : singularCochainGroup K X a) (β : singularCochainGroup K X b) :
    singularCochainGroup K X n :=
  cochainOfFun n (fun σ => ∑ S ∈ cutIndex 2 n,
    cupOneSign K S * (faceVal a α σ (cutU S) * faceVal b β σ (cutV S)))

@[simp] theorem cochainCupOne_eval {K : Type} [CommRing K] {X : TopCat.{0}} (a b n : ℕ)
    (α : singularCochainGroup K X a) (β : singularCochainGroup K X b)
    (σ : singularSimplices X n) :
    cochainEval n (cochainCupOne a b n α β) σ
      = ∑ S ∈ cutIndex 2 n,
          cupOneSign K S * (faceVal a α σ (cutU S) * faceVal b β σ (cutV S)) :=
  cochainEval_cochainOfFun n _ σ

/-- **Degree bookkeeping is automatic.**  Outside the bidegree `a + b = n + 1` the
signed cup-1 product is the zero cochain. -/
theorem cochainCupOne_of_degree_ne {K : Type} [CommRing K] {X : TopCat.{0}} (a b n : ℕ)
    (hab : ¬ a + b = n + 1)
    (α : singularCochainGroup K X a) (β : singularCochainGroup K X b) :
    cochainCupOne a b n α β = 0 := by
  apply cochain_ext
  intro σ
  rw [cochainCupOne_eval, cochainEval_zero]
  refine Finset.sum_eq_zero fun S hS => ?_
  by_cases hU : (cutU S).card = a + 1
  · refine mul_eq_zero_of_right _ (mul_eq_zero_of_right _ (faceVal_of_card_ne β σ ?_))
    have hcount := cutU_card_add_cutV_card S
    have hcard := card_of_mem_cutIndex hS
    omega
  · exact mul_eq_zero_of_right _ (mul_eq_zero_of_left (faceVal_of_card_ne α σ hU) _)

@[simp] theorem cochainCupOne_zero_left {K : Type} [CommRing K] {X : TopCat.{0}} (a b n : ℕ)
    (β : singularCochainGroup K X b) :
    cochainCupOne a b n (0 : singularCochainGroup K X a) β = 0 := by
  apply cochain_ext
  intro σ
  rw [cochainCupOne_eval, cochainEval_zero]
  refine Finset.sum_eq_zero fun S _ => ?_
  rw [faceVal_zero, zero_mul, mul_zero]

@[simp] theorem cochainCupOne_zero_right {K : Type} [CommRing K] {X : TopCat.{0}} (a b n : ℕ)
    (α : singularCochainGroup K X a) :
    cochainCupOne a b n α (0 : singularCochainGroup K X b) = 0 := by
  apply cochain_ext
  intro σ
  rw [cochainCupOne_eval, cochainEval_zero]
  refine Finset.sum_eq_zero fun S _ => ?_
  rw [faceVal_zero, mul_zero, mul_zero]

/-! ## 4. A generic restatement

The `ZMod 2` statement of `SteenrodCupOne.cochainCupI_zero_zero_comm` with the
coefficient freed; its proof there uses no characteristic-two step.  The two degree-cast
lemmas this lane also needs live in `CupOneComm.lean`, which is where `cochainCast_rfl`
is in scope. -/

/-- **The bidegree-`(0,0)` cup product is commutative on the nose**, over any
commutative ring: the only `1`-cut of a `0`-simplex uses the whole vertex set for both
families. -/
theorem cochainCupI_zero_zero_comm_of {K : Type} [CommRing K] {X : TopCat.{0}}
    (φ ψ : singularCochainGroup K X 0) :
    cochainCupI 0 0 0 0 φ ψ = cochainCupI 0 0 0 0 ψ φ := by
  apply cochain_ext
  intro τ
  rw [cochainCupI_eval, cochainCupI_eval, cutIndex_self, Finset.sum_singleton,
    Finset.sum_singleton, cutU_univ, cutV_univ]
  exact mul_comm _ _

end

end CharClass
end GroupApproximation
