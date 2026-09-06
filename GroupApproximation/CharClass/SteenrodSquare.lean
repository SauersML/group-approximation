import GroupApproximation.CharClass.SteenrodCupOne
import Mathlib.Algebra.Module.ZMod

/-!
# The Steenrod squares `Sq^k` on mod-2 cohomology

`Sq^k [α] = [α ⌣_{n-k} α]` for `α` an `n`-cocycle.  The construction never needs
the exactness statement "a cocycle with zero class is a coboundary": the map
`α ↦ [α ⌣_i α]` is additive **on cocycles** (the cross terms form a coboundary,
by the cup-`i` coboundary formula) and kills coboundaries (because `δη ⌣_i δη`
is itself a coboundary), so it descends through the cokernel presentation of
homology exactly as the vendored `cupHomologyLeft` does for the cup product.

## Degrees

`Sq k` on `Hmod2 X n` lands in `Hmod2 X (k + n)`, built from
`cochainCupI (n - k) n n (k + n)`.  The bidegree condition `a + b = m + i` reads
`n + n = (k + n) + (n - k)`, which holds exactly when `k ≤ n`; for `k > n` the
truncated subtraction gives `n - k = 0`, the condition fails, and
`cochainCupI_of_degree_ne` makes the cochain the zero cochain.  So **instability
is free**: no `dite` appears in the definition of `Sq`.

The target is `k + n` rather than `n + k` on purpose.  The coboundary case of the
cokernel condition needs the predecessor of the output degree, and `k + (j + 1)`
reduces to `(k + j) + 1` definitionally while `(j + 1) + k` does not reduce at
all for a variable `k`.  Choosing `k + n` removes a degree cast that would
otherwise have to be carried through the whole descent.  Downstream, `cohCast`
converts to `n + k` in one step.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass

noncomputable section

variable {X : TopCat.{0}}

/-! ## 1. Characteristic two on cochains -/

theorem cochain_add_self (m : ℕ) (φ : singularCochainGroup (ZMod 2) X m) : φ + φ = 0 := by
  apply cochain_ext
  intro τ
  rw [cochainEval_add, cochainEval_zero]
  have h2 : ∀ y : ZMod 2, y + y = 0 := by decide
  exact h2 _

theorem cochainCoboundary_add (m : ℕ) (φ ψ : singularCochainGroup (ZMod 2) X m) :
    cochainCoboundary (ZMod 2) X m (φ + ψ)
      = cochainCoboundary (ZMod 2) X m φ + cochainCoboundary (ZMod 2) X m ψ := by
  unfold cochainCoboundary
  exact map_add _ _ _

/-! ## 2. The diagonal cup-`i` -/

/-- **`α ⌣ᵢ α` is a cocycle**, at every literal output degree.  For `i = 0` this
is the Leibniz case; for `i = j+1` the two low terms of the coboundary formula
are *the same* term and cancel mod 2. -/
theorem cochainCupI_self_cocycle (i a n : ℕ) (α : singularCochainGroup (ZMod 2) X a)
    (hα : cochainCoboundary (ZMod 2) X a α = 0) :
    cochainCoboundary (ZMod 2) X n (cochainCupI i a a n α α) = 0 := by
  cases i with
  | zero => exact cochainCupI_zero_cocycle a a n α hα α hα
  | succ j =>
      rw [cochainCupI_coboundary j a a n α α, hα, cochainCupI_zero_left,
        cochainCupI_zero_right]
      simp only [zero_add]
      exact cochain_add_self _ _

/-- **The cross terms of a diagonal cup-`i` form a coboundary**, for cocycles. -/
theorem cochainCupI_cross (i p q n : ℕ) (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0) (ψ : singularCochainGroup (ZMod 2) X q)
    (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    cochainCupI i p q (n + 1) φ ψ + cochainCupI i q p (n + 1) ψ φ
      = cochainCoboundary (ZMod 2) X n (cochainCupI (i + 1) p q n φ ψ) := by
  have h := cochainCupI_coboundary i p q n φ ψ
  rw [hφ, hψ, cochainCupI_zero_left, cochainCupI_zero_right] at h
  simp only [zero_add] at h
  exact h.symm

/-- The coboundary of a diagonal cup-`i`, for an arbitrary cochain: the two low
terms cancel, leaving the two Leibniz terms. -/
theorem coboundary_cochainCupI_self (j m n : ℕ) (η : singularCochainGroup (ZMod 2) X m) :
    cochainCoboundary (ZMod 2) X n (cochainCupI j m m n η η)
      = cochainCupI j (m + 1) m (n + 1) (cochainCoboundary (ZMod 2) X m η) η
        + cochainCupI j m (m + 1) (n + 1) η (cochainCoboundary (ZMod 2) X m η) := by
  cases j with
  | zero => exact cochainCupI_coboundary_zero m m n η η
  | succ l =>
      rw [cochainCupI_coboundary l m m n η η]
      have hrw : ∀ A B C : singularCochainGroup (ZMod 2) X (n + 1),
          A + B + C + C = A + B := by
        intro A B C
        have h1 : A + B + C + C = A + B + (C + C) := by abel
        rw [h1, cochain_add_self, add_zero]
      exact hrw _ _ _

/-- **`δη ⌣ᵢ δη` is a coboundary.**  This is the cokernel condition that lets
`Sq` descend to cohomology. -/
theorem exists_coboundary_cochainCupI_self (i m n : ℕ)
    (η : singularCochainGroup (ZMod 2) X m) :
    ∃ ζ : singularCochainGroup (ZMod 2) X n,
      cochainCupI i (m + 1) (m + 1) (n + 1) (cochainCoboundary (ZMod 2) X m η)
          (cochainCoboundary (ZMod 2) X m η)
        = cochainCoboundary (ZMod 2) X n ζ := by
  have hdd : cochainCoboundary (ZMod 2) X (m + 1) (cochainCoboundary (ZMod 2) X m η) = 0 :=
    cochainCoboundary_cochainCoboundary X m η
  cases i with
  | zero =>
      refine ⟨cochainCupI 0 m (m + 1) n η (cochainCoboundary (ZMod 2) X m η), ?_⟩
      rw [cochainCupI_coboundary_zero m (m + 1) n η (cochainCoboundary (ZMod 2) X m η), hdd,
        cochainCupI_zero_right, add_zero]
  | succ j =>
      refine ⟨cochainCupI (j + 1) m (m + 1) n η (cochainCoboundary (ZMod 2) X m η)
        + cochainCupI j m m n η η, ?_⟩
      rw [cochainCoboundary_add,
        cochainCupI_coboundary j m (m + 1) n η (cochainCoboundary (ZMod 2) X m η), hdd,
        cochainCupI_zero_right, coboundary_cochainCupI_self j m n η]
      have hrw : ∀ A C D : singularCochainGroup (ZMod 2) X (n + 1),
          A + 0 + C + D + (D + C) = A := by
        intro A C D
        have h1 : A + 0 + C + D + (D + C) = A + (C + C) + (D + D) := by abel
        rw [h1, cochain_add_self, cochain_add_self, add_zero, add_zero]
      exact (hrw _ _ _).symm

/-! ## 3. The cross terms have zero class -/

/-- At output degree `0` a diagonal cup-`i` is symmetric: the only cut set that
can occur uses the single vertex of a `0`-simplex for both families. -/
theorem cochainCupI_comm_degree_zero (i n : ℕ) (φ ψ : singularCochainGroup (ZMod 2) X n) :
    cochainCupI i n n 0 φ ψ = cochainCupI i n n 0 ψ φ := by
  apply cochain_ext
  intro τ
  rw [cochainCupI_eval, cochainCupI_eval]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hcard : S.card = i + 1 := card_of_mem_cutIndex hS
  have hle : S.card ≤ 1 := by simpa using Finset.card_le_univ S
  have hi : i = 0 := by omega
  subst hi
  have huniv : S = (Finset.univ : Finset (Fin 1)) := by
    refine (Finset.card_eq_iff_eq_univ S).1 ?_
    rw [hcard]
    simp
  subst huniv
  rw [cutU_univ 0, cutV_univ 0]
  exact mul_comm _ _

theorem cocycleClass_cochainCupI_cross_zero (i n m : ℕ)
    (φ : singularCochainGroup (ZMod 2) X n) (hφ : cochainCoboundary (ZMod 2) X n φ = 0)
    (ψ : singularCochainGroup (ZMod 2) X n) (hψ : cochainCoboundary (ZMod 2) X n ψ = 0)
    (hcoc : cochainCoboundary (ZMod 2) X m
        (cochainCupI i n n m φ ψ + cochainCupI i n n m ψ φ) = 0) :
    cocycleClass X m (cochainCupI i n n m φ ψ + cochainCupI i n n m ψ φ) hcoc = 0 := by
  cases m with
  | zero =>
      have hz : cochainCupI i n n 0 φ ψ + cochainCupI i n n 0 ψ φ = 0 := by
        rw [cochainCupI_comm_degree_zero i n φ ψ]
        exact cochain_add_self _ _
      exact cocycleClass_eq_zero_of_eq X 0 hz hcoc (map_zero _)
        (cocycleClass_zero X 0 (map_zero _))
  | succ m' =>
      refine cocycleClass_eq_zero_of_eq X (m' + 1)
        (cochainCupI_cross i n n m' φ hφ ψ hψ) hcoc
        (cochainCoboundary_cochainCoboundary X m' _) ?_
      exact cocycleClass_coboundary_zero X m' (cochainCupI (i + 1) n n m' φ ψ) _

/-! ## 4. The square on cocycles -/

/-- The cochain square: `α ⌣_{n-k} α`, of degree `k + n`. -/
def sqCochain (n k : ℕ) (φ : singularCochainGroup (ZMod 2) X n) :
    singularCochainGroup (ZMod 2) X (k + n) :=
  cochainCupI (n - k) n n (k + n) φ φ

theorem sqCochain_cocycle (n k : ℕ) (φ : singularCochainGroup (ZMod 2) X n)
    (hφ : cochainCoboundary (ZMod 2) X n φ = 0) :
    cochainCoboundary (ZMod 2) X (k + n) (sqCochain n k φ) = 0 :=
  cochainCupI_self_cocycle (n - k) n (k + n) φ hφ

/-- **Additivity on cocycles.** -/
theorem cocycleClass_sqCochain_add (n k : ℕ)
    (φ : singularCochainGroup (ZMod 2) X n) (hφ : cochainCoboundary (ZMod 2) X n φ = 0)
    (ψ : singularCochainGroup (ZMod 2) X n) (hψ : cochainCoboundary (ZMod 2) X n ψ = 0)
    (hsum : cochainCoboundary (ZMod 2) X (k + n) (sqCochain n k (φ + ψ)) = 0) :
    cocycleClass X (k + n) (sqCochain n k (φ + ψ)) hsum
      = cocycleClass X (k + n) (sqCochain n k φ) (sqCochain_cocycle n k φ hφ)
        + cocycleClass X (k + n) (sqCochain n k ψ) (sqCochain_cocycle n k ψ hψ) := by
  have hsplit : sqCochain n k (φ + ψ)
      = (sqCochain n k φ + sqCochain n k ψ)
        + (cochainCupI (n - k) n n (k + n) φ ψ + cochainCupI (n - k) n n (k + n) ψ φ) := by
    unfold sqCochain
    rw [cochainCupI_add_left, cochainCupI_add_right, cochainCupI_add_right]
    abel
  have hpair : cochainCoboundary (ZMod 2) X (k + n) (sqCochain n k φ + sqCochain n k ψ) = 0 := by
    rw [cochainCoboundary_add, sqCochain_cocycle n k φ hφ, sqCochain_cocycle n k ψ hψ, add_zero]
  have hcross : cochainCoboundary (ZMod 2) X (k + n)
      (cochainCupI (n - k) n n (k + n) φ ψ + cochainCupI (n - k) n n (k + n) ψ φ) = 0 := by
    have hs := hsum
    rw [hsplit, cochainCoboundary_add, hpair, zero_add] at hs
    exact hs
  rw [cocycleClass_congr X (k + n) hsplit hsum
      (by rw [cochainCoboundary_add, hpair, hcross, add_zero]),
    cocycleClass_add X (k + n) _ _ hpair hcross _,
    cocycleClass_cochainCupI_cross_zero (n - k) n (k + n) φ hφ ψ hψ hcross, add_zero,
    cocycleClass_add X (k + n) _ _ (sqCochain_cocycle n k φ hφ)
      (sqCochain_cocycle n k ψ hψ) hpair]

/-! ## 5. Descent to cohomology -/

/-- The square as an additive map on cycles. -/
def sqAddHom (X : TopCat.{0}) (n k : ℕ) :
    (cochainCxZMod2 X).cycles n →+ cohomologyZMod2 X (k + n) :=
  AddMonoidHom.mk'
    (fun c => cocycleClass X (k + n) (sqCochain n k (((cochainCxZMod2 X).iCycles n).hom c))
      (sqCochain_cocycle n k _ (cochainCoboundary_iCycles X n c)))
    (by
      intro c₁ c₂
      have hval : ((cochainCxZMod2 X).iCycles n).hom (c₁ + c₂)
          = ((cochainCxZMod2 X).iCycles n).hom c₁ + ((cochainCxZMod2 X).iCycles n).hom c₂ :=
        map_add _ _ _
      have h1 : cochainCoboundary (ZMod 2) X n
          (((cochainCxZMod2 X).iCycles n).hom c₁ + ((cochainCxZMod2 X).iCycles n).hom c₂) = 0 :=
        hval ▸ cochainCoboundary_iCycles X n (c₁ + c₂)
      rw [cocycleClass_congr X (k + n) (congrArg (sqCochain n k) hval) _
        (sqCochain_cocycle n k _ h1)]
      exact cocycleClass_sqCochain_add n k _ (cochainCoboundary_iCycles X n c₁) _
        (cochainCoboundary_iCycles X n c₂) _)

/-- The square as a `ModuleCat` morphism on cycles: over `ZMod 2` every additive
map is linear. -/
def sqMor (X : TopCat.{0}) (n k : ℕ) :
    (cochainCxZMod2 X).cycles n ⟶ cohomologyZMod2 X (k + n) :=
  ModuleCat.ofHom ((sqAddHom X n k).toZModLinearMap 2)

theorem sqMor_hom (X : TopCat.{0}) (n k : ℕ) (c : (cochainCxZMod2 X).cycles n) :
    (sqMor X n k).hom c
      = cocycleClass X (k + n) (sqCochain n k (((cochainCxZMod2 X).iCycles n).hom c))
          (sqCochain_cocycle n k _ (cochainCoboundary_iCycles X n c)) := rfl

/-- The square of a cochain in the image of a differential has zero class, for
any source index.  The `Rel` case is `δη ⌣ᵢ δη` being a coboundary; the other
case is the differential being zero. -/
theorem cocycleClass_sqCochain_d_zero (X : TopCat.{0}) (n k j : ℕ)
    (η : (cochainCxZMod2 X).X j)
    (hcoc : cochainCoboundary (ZMod 2) X (k + n)
        (sqCochain n k (((cochainCxZMod2 X).d j n).hom η)) = 0) :
    cocycleClass X (k + n) (sqCochain n k (((cochainCxZMod2 X).d j n).hom η)) hcoc = 0 := by
  by_cases hrel : (ComplexShape.up ℕ).Rel j n
  · obtain rfl : j + 1 = n := hrel
    obtain ⟨ζ, hζ⟩ := exists_coboundary_cochainCupI_self (j + 1 - k) j (k + j) η
    exact cocycleClass_eq_zero_of_eq X (k + (j + 1)) hζ hcoc
      (cochainCoboundary_cochainCoboundary X (k + j) ζ)
      (cocycleClass_coboundary_zero X (k + j) ζ
        (cochainCoboundary_cochainCoboundary X (k + j) ζ))
  · have h0 : ((cochainCxZMod2 X).d j n).hom η = 0 := by
      rw [(cochainCxZMod2 X).shape j n hrel]
      simp
    have hz : sqCochain n k (((cochainCxZMod2 X).d j n).hom η) = 0 := by
      rw [h0]
      unfold sqCochain
      exact cochainCupI_zero_left _ _ _ _ _
    exact cocycleClass_eq_zero_of_eq X (k + n) hz hcoc (map_zero _)
      (cocycleClass_zero X (k + n) (map_zero _))

/-- **The cokernel condition.** -/
theorem sqMor_toCycles (X : TopCat.{0}) (n k : ℕ) :
    (cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev n) n ≫ sqMor X n k = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro η
  show (sqMor X n k).hom
      (((cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev n) n).hom η) = 0
  rw [sqMor_hom]
  have heq : ((cochainCxZMod2 X).iCycles n).hom
        (((cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev n) n).hom η)
      = ((cochainCxZMod2 X).d ((ComplexShape.up ℕ).prev n) n).hom η := by
    rw [← ModuleCat.comp_apply, (cochainCxZMod2 X).toCycles_i]
  refine cocycleClass_eq_zero_of_eq X (k + n) (congrArg (sqCochain n k) heq) _ ?_ ?_
  · rw [← congrArg (sqCochain n k) heq]
    exact sqCochain_cocycle n k _ (cochainCoboundary_iCycles X n _)
  · exact cocycleClass_sqCochain_d_zero X n k ((ComplexShape.up ℕ).prev n) η _

/-- **The Steenrod square** `Sq^k : H^n(X; F₂) ⟶ H^{k+n}(X; F₂)`. -/
def sqHomology (X : TopCat.{0}) (n k : ℕ) :
    cohomologyZMod2 X n ⟶ cohomologyZMod2 X (k + n) :=
  ((cochainCxZMod2 X).homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl).desc
    (CokernelCofork.ofπ (sqMor X n k) (sqMor_toCycles X n k))

theorem homologyπ_sqHomology (X : TopCat.{0}) (n k : ℕ) :
    (cochainCxZMod2 X).homologyπ n ≫ sqHomology X n k = sqMor X n k :=
  ((cochainCxZMod2 X).homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl).fac
    (CokernelCofork.ofπ (sqMor X n k) (sqMor_toCycles X n k))
    WalkingParallelPair.one

/-- `Sq^k` as a function on classes, in `cc-cohom-api`'s vocabulary. -/
def Sq (k : ℕ) {n : ℕ} (x : Hmod2 X n) : Hmod2 X (k + n) :=
  (sqHomology X n k).hom x

/-- **Computation rule.**  `Sq^k` of the class of a cocycle is the class of its
cup-`(n-k)` square. -/
theorem Sq_mk (k n : ℕ) (φ : singularCochainGroup (ZMod 2) X n)
    (hφ : cochainCoboundary (ZMod 2) X n φ = 0) :
    Sq k (cocycleClass X n φ hφ)
      = cocycleClass X (k + n) (sqCochain n k φ) (sqCochain_cocycle n k φ hφ) := by
  show (sqHomology X n k).hom (((cochainCxZMod2 X).homologyπ n).hom _) = _
  rw [← ModuleCat.comp_apply, homologyπ_sqHomology, sqMor_hom]
  exact cocycleClass_congr X (k + n)
    (congrArg (sqCochain n k) (iCycles_cyclesMk X n φ hφ)) _ _

/-- **Instability.**  `Sq^k` vanishes above the degree, because the bidegree
condition `n + n = (k + n) + (n - k)` fails once `k > n`. -/
theorem Sq_eq_zero_of_lt (k n : ℕ) (hk : n < k) (x : Hmod2 X n) : Sq k x = 0 := by
  obtain ⟨φ, hφ, rfl⟩ := exists_cocycle x
  rw [Sq_mk]
  have hz : sqCochain n k φ = 0 := by
    unfold sqCochain
    refine cochainCupI_of_degree_ne (n - k) n n (k + n) ?_ φ φ
    omega
  exact cocycleClass_eq_zero_of_eq X (k + n) hz _ (map_zero _)
    (cocycleClass_zero X (k + n) (map_zero _))

/-- **Additivity.** -/
theorem Sq_add (k n : ℕ) (x y : Hmod2 X n) : Sq k (x + y) = Sq k x + Sq k y :=
  map_add (sqHomology X n k).hom x y

/-- **`Sq^n` is the cup square.**  At `k = n` the cup index is `0`, which is the
Alexander–Whitney cup product on the nose. -/
theorem Sq_self (n : ℕ) (x : Hmod2 X n) : Sq n x = cohCast (Nat.add_comm n n) (cup x x) := by
  obtain ⟨φ, hφ, rfl⟩ := exists_cocycle x
  rw [Sq_mk, cup_mk, cohCast_cocycleClass (Nat.add_comm n n) (cochainCup n n φ φ)
    (cochainCupZMod2_respects_cocycles n n φ φ hφ hφ)
    (by rw [cochainCast_cochainCupI_zero n n (n + n) (Nat.add_comm n n) φ φ]
        exact cochainCupI_zero_cocycle n n (n + n) φ hφ φ hφ)]
  refine cocycleClass_congr X (n + n) ?_ _ _
  rw [cochainCast_cochainCupI_zero n n (n + n) (Nat.add_comm n n) φ φ]
  unfold sqCochain
  rw [Nat.sub_self]

/-- **`Sq^0` is the identity.**  At `k = 0` the cup index is `n`, and the only
`n`-cut of an `n`-simplex uses every vertex for both families. -/
theorem Sq_zero (n : ℕ) (x : Hmod2 X n) : Sq 0 x = x := by
  obtain ⟨φ, hφ, rfl⟩ := exists_cocycle x
  rw [Sq_mk]
  refine cocycleClass_congr X (0 + n) ?_ _ _
  unfold sqCochain
  rw [Nat.sub_zero]
  exact cochainCupI_self n φ

end

end CharClass
end GroupApproximation
