import GroupApproximation.CharClass.OddPProductEval
import GroupApproximation.CharClass.OddPEvalMultilinear
import GroupApproximation.CharClass.OddPTopPowerAWChain
import GroupApproximation.CharClass.OddPDiagonalSrc
import GroupApproximation.Meta.AxiomGuard

/-!
# The slotwise Alexander–Whitney map on the flat tuple model

Item 3 of the Cartan comparison at odd `p` (`lx-cartan-b`'s lemma list).  `awTupAll K X r` sends a
tuple of `r` tagged simplices to the sum, over every choice of a cut in every slot, of the
`2r`-tuple whose slot `2j` is the front of slot `j` and whose slot `2j + 1` is its back.  No sign:
the binary Alexander–Whitney map has degree `0`, and the Koszul prefix of slot `2j` of the image is
the prefix of slot `j` of the source.

## Main results

* `gCupFun` — the graded Alexander–Whitney cup of two graded cochains, cast-free, with its value
  (`tagEvalG_gCupFun`), homogeneity (`gCupFun_of_ne`), the bridge `gCupFun_piSingle` to
  `cochainCup`, and the Leibniz formula `gCoboundary_gCupFun` (from `TopPow.binary_aw`).
* `tupEvalAll_awTupAll` — evaluating interleaved cochains on the image is evaluating the slotwise
  cups.
* `tupDAll_awTupAll` — a chain map, by separation (`tupAllMod_eq_of_eval`).
* `awTupAll_tupTAll` — the cyclic operator becomes its square.
* `tupAllMap_awTupAll` — natural in the space.
* the degree-`k` twin `awTup`, with `tupIncl_comp_awTup`, `awTup_tupD`, `awTup_tupT`, `awTup_tupMap`,
  `awTup_diagPt`.

## Design

The faces of the interface are cast-free `restrictSimplex` faces indexed by `i : Fin (n + 1)`
(`awFront`, `awBack`); the proofs run through `OddPTopPowerAW`'s clamped faces `TopPow.awFront`,
`TopPow.awBack`, which are functions of a natural cut, and the two are identified by
`awFront_eq_topPow`, `awBack_eq_topPow`.  The tuple itself uses natural cuts `c : Fin r → ℕ` from
`Fintype.piFinset`, so reindexing along the rotation never meets a dependent type.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Simplicial
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-! ## 1. Cast-free faces -/

section Faces

variable {X : TopCat.{0}}

/-- The front face `⦋i⦌ ⟶ ⦋n⦌`, `x ↦ x`. -/
def awFrontHom (n : ℕ) (i : Fin (n + 1)) : (⦋i.val⦌ : SimplexCategory) ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom
    ⟨fun x => ⟨x.val, by have := x.isLt; have := i.isLt; omega⟩, fun x y hxy => by
      show x.val ≤ y.val
      exact hxy⟩

/-- The back face `⦋n − i⦌ ⟶ ⦋n⦌`, `x ↦ x + i`. -/
def awBackHom (n : ℕ) (i : Fin (n + 1)) : (⦋n - i.val⦌ : SimplexCategory) ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom
    ⟨fun x => ⟨x.val + i.val, by have := x.isLt; have := i.isLt; omega⟩, fun x y hxy => by
      show x.val + i.val ≤ y.val + i.val
      exact Nat.add_le_add_right hxy _⟩

variable (X)

/-- The front face `σ[0..i]` of a singular `n`-simplex. -/
def awFront (n : ℕ) (i : Fin (n + 1)) (σ : singularSimplices X n) : singularSimplices X i.val :=
  restrictSimplex (awFrontHom n i) σ

/-- The back face `σ[i..n]` of a singular `n`-simplex. -/
def awBack (n : ℕ) (i : Fin (n + 1)) (σ : singularSimplices X n) :
    singularSimplices X (n - i.val) :=
  restrictSimplex (awBackHom n i) σ

variable {X}

theorem awFront_natural {Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (i : Fin (n + 1))
    (σ : singularSimplices X n) :
    pushSimplex f i.val (awFront X n i σ) = awFront Y n i (pushSimplex f n σ) :=
  restrictSimplex_naturality f (awFrontHom n i) σ

theorem awBack_natural {Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (i : Fin (n + 1))
    (σ : singularSimplices X n) :
    pushSimplex f (n - i.val) (awBack X n i σ) = awBack Y n i (pushSimplex f n σ) :=
  restrictSimplex_naturality f (awBackHom n i) σ

/-- The cast-free front face is the clamped front face of `OddPTopPowerAW`. -/
theorem awFront_eq_topPow (n : ℕ) (i : Fin (n + 1)) (σ : singularSimplices X n) :
    (⟨i.val, awFront X n i σ⟩ : TagSimp X) = TopPow.awFront (⟨n, σ⟩ : TagSimp X) i.val := by
  have h : awFrontHom n i = TopPow.clampHom i.val n id monotone_id := by
    ext x : 3
    apply Fin.ext
    rw [TopPow.clampHom_apply]
    show x.val = min (id x.val) n
    have := x.isLt
    have := i.isLt
    simp only [id_eq]
    omega
  show (⟨i.val, restrictSimplex (awFrontHom n i) σ⟩ : TagSimp X)
    = ⟨i.val, (TopCat.toSSet.obj X).map (TopPow.clampHom i.val n id monotone_id).op σ⟩
  rw [h]
  rfl

/-- The cast-free back face is the clamped back face of `OddPTopPowerAW`. -/
theorem awBack_eq_topPow (n : ℕ) (i : Fin (n + 1)) (σ : singularSimplices X n) :
    (⟨n - i.val, awBack X n i σ⟩ : TagSimp X) = TopPow.awBack (⟨n, σ⟩ : TagSimp X) i.val := by
  have h : awBackHom n i
      = TopPow.clampHom (n - i.val) n (fun j => j + i.val) (TopPow.addRight_mono i.val) := by
    ext x : 3
    apply Fin.ext
    rw [TopPow.clampHom_apply]
    show x.val + i.val = min (x.val + i.val) n
    have := x.isLt
    have := i.isLt
    omega
  show (⟨n - i.val, restrictSimplex (awBackHom n i) σ⟩ : TagSimp X)
    = ⟨n - i.val, (TopCat.toSSet.obj X).map
        (TopPow.clampHom (n - i.val) n (fun j => j + i.val) (TopPow.addRight_mono i.val)).op σ⟩
  rw [h]
  rfl

/-- A simplex is its own clamped sub-simplex on the identity vertex map. -/
theorem vtx_id_self {k : ℕ} (σ : singularSimplices X k) :
    TopPow.vtx σ k id monotone_id = ⟨k, σ⟩ := by
  have h : TopPow.clampHom k k id monotone_id = 𝟙 _ := by
    ext j : 3
    apply Fin.ext
    rw [TopPow.clampHom_apply]
    exact min_eq_left (Nat.le_of_lt_succ j.isLt)
  show (⟨k, (TopCat.toSSet.obj X).map (TopPow.clampHom k k id monotone_id).op σ⟩ : TagSimp X)
    = ⟨k, σ⟩
  rw [h, op_id, FunctorToTypes.map_id_apply]

end Faces

/-! ## 2. The graded Alexander–Whitney cup -/

section Cup

variable (K : Type) [CommRing K] {X : TopCat.{0}}

/-- **The graded cup** of two graded cochains: in degree `n`, `σ ↦ Σ_i φ(σ[0..i]) ψ(σ[i..n])`. -/
def gCupFun (φ ψ : ∀ n : ℕ, singularCochainGroup K X n) : ∀ n : ℕ, singularCochainGroup K X n :=
  fun n => cochainOfFun n (fun σ => ∑ i : Fin (n + 1),
    tagEvalG K φ (⟨i.val, awFront X n i σ⟩ : TagSimp X)
      * tagEvalG K ψ (⟨n - i.val, awBack X n i σ⟩ : TagSimp X))

theorem tagEvalG_gCupFun (φ ψ : ∀ n : ℕ, singularCochainGroup K X n) (n : ℕ)
    (σ : singularSimplices X n) :
    tagEvalG K (gCupFun K φ ψ) (⟨n, σ⟩ : TagSimp X)
      = ∑ i : Fin (n + 1), tagEvalG K φ (⟨i.val, awFront X n i σ⟩ : TagSimp X)
          * tagEvalG K ψ (⟨n - i.val, awBack X n i σ⟩ : TagSimp X) :=
  cochainEval_cochainOfFun n _ σ

/-- The value of the graded cup through the clamped faces, as a `range` sum. -/
theorem tagEvalG_gCupFun_range (φ ψ : ∀ n : ℕ, singularCochainGroup K X n) (τ : TagSimp X) :
    tagEvalG K (gCupFun K φ ψ) τ
      = ∑ m ∈ Finset.range (τ.1 + 1),
          tagEvalG K φ (TopPow.awFront τ m) * tagEvalG K ψ (TopPow.awBack τ m) := by
  obtain ⟨n, σ⟩ := τ
  rw [tagEvalG_gCupFun, ← Fin.sum_univ_eq_sum_range (fun m =>
    tagEvalG K φ (TopPow.awFront (⟨n, σ⟩ : TagSimp X) m)
      * tagEvalG K ψ (TopPow.awBack (⟨n, σ⟩ : TagSimp X) m)) (n + 1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg₂ (· * ·) (congrArg (tagEvalG K φ) (awFront_eq_topPow n i σ))
    (congrArg (tagEvalG K ψ) (awBack_eq_topPow n i σ))

/-- **Homogeneity**: the cup of cochains concentrated in degrees `d`, `d'` is concentrated in
degree `d + d'`. -/
theorem gCupFun_of_ne (φ ψ : ∀ n : ℕ, singularCochainGroup K X n) {d d' n : ℕ}
    (hφ : ∀ m, m ≠ d → φ m = 0) (hψ : ∀ m, m ≠ d' → ψ m = 0) (hn : n ≠ d + d') :
    gCupFun K φ ψ n = 0 := by
  apply cochain_ext
  intro σ
  rw [cochainEval_zero]
  show tagEvalG K (gCupFun K φ ψ) (⟨n, σ⟩ : TagSimp X) = 0
  rw [tagEvalG_gCupFun]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi := i.isLt
  by_cases hid : i.val = d
  · have h2 : n - i.val ≠ d' := by omega
    rw [tagEvalG_of_eq_zero K ψ _ (hψ _ h2), mul_zero]
  · rw [tagEvalG_of_eq_zero K φ _ (hφ _ hid), zero_mul]

/-- **The bridge to `cochainCup`.** -/
theorem gCupFun_piSingle (d d' : ℕ) (u : singularCochainGroup K X d)
    (v : singularCochainGroup K X d') :
    gCupFun K (Pi.single d u) (Pi.single d' v) = Pi.single (d + d') (cochainCup d d' u v) := by
  funext n
  by_cases hn : n = d + d'
  · subst hn
    rw [Pi.single_eq_same]
    apply cochain_ext
    intro σ
    rw [cochainCup_eval]
    show tagEvalG K (gCupFun K (Pi.single d u) (Pi.single d' v)) (⟨d + d', σ⟩ : TagSimp X) = _
    have hd : d < d + d' + 1 := by omega
    rw [tagEvalG_gCupFun, Finset.sum_eq_single (⟨d, hd⟩ : Fin (d + d' + 1))]
    · have hfh : awFrontHom (d + d') ⟨d, hd⟩ = AlexanderWhitney.frontFace d d' := by
        ext x : 3
        apply Fin.ext
        rw [AlexanderWhitney.frontFace_apply]
        rfl
      have hf : (⟨d, awFront X (d + d') ⟨d, hd⟩ σ⟩ : TagSimp X) = ⟨d, frontSimplex X d d' σ⟩ := by
        show (⟨d, restrictSimplex (awFrontHom (d + d') ⟨d, hd⟩) σ⟩ : TagSimp X)
          = ⟨d, (TopCat.toSSet.obj X).map (AlexanderWhitney.frontFace d d').op σ⟩
        rw [hfh]
        rfl
      have hbh : TopPow.clampHom d' (d + d') (fun j => j + d) (TopPow.addRight_mono d)
          = AlexanderWhitney.backFace d d' := by
        ext x : 3
        apply Fin.ext
        rw [TopPow.clampHom_apply, AlexanderWhitney.backFace_apply]
        have := x.isLt
        show min (x.val + d) (d + d') = x.val + d
        omega
      have hb : (⟨d + d' - d, awBack X (d + d') ⟨d, hd⟩ σ⟩ : TagSimp X)
          = ⟨d', backSimplex X d d' σ⟩ := by
        refine (awBack_eq_topPow (d + d') ⟨d, hd⟩ σ).trans ?_
        refine (TopPow.vtx_congr σ (TopPow.addRight_mono d) (TopPow.addRight_mono d)
          (show d + d' - d = d' by omega) fun _ _ => rfl).trans ?_
        show (⟨d', (TopCat.toSSet.obj X).map
            (TopPow.clampHom d' (d + d') (fun j => j + d) (TopPow.addRight_mono d)).op σ⟩ : TagSimp X)
          = ⟨d', (TopCat.toSSet.obj X).map (AlexanderWhitney.backFace d d').op σ⟩
        rw [hbh]
      refine (congrArg₂ (· * ·) (congrArg (tagEvalG K (Pi.single d u)) hf)
        (congrArg (tagEvalG K (Pi.single d' v)) hb)).trans ?_
      show cochainEval d (Pi.single d u d) (frontSimplex X d d' σ)
          * cochainEval d' (Pi.single d' v d') (backSimplex X d d' σ) = _
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · intro i _ hi
      have hid : i.val ≠ d := fun h => hi (Fin.ext h)
      rw [tagEvalG_of_eq_zero K _ _ (Pi.single_eq_of_ne hid u), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Pi.single_eq_of_ne hn]
    exact gCupFun_of_ne K _ _ (fun m hm => Pi.single_eq_of_ne hm u)
      (fun m hm => Pi.single_eq_of_ne hm v) hn

/-- The graded sign twist `φ ↦ (−1)^n φ_n`. -/
def gSign (φ : ∀ n : ℕ, singularCochainGroup K X n) : ∀ n : ℕ, singularCochainGroup K X n :=
  fun n => (-1 : K) ^ n • φ n

theorem tagEvalG_gSign (φ : ∀ n : ℕ, singularCochainGroup K X n) (τ : TagSimp X) :
    tagEvalG K (gSign K φ) τ = (-1 : K) ^ τ.1 * tagEvalG K φ τ :=
  cochainEval_smul τ.1 _ (φ τ.1) τ.2

/-- One slot of E4: a graded cochain summed over the boundary of a tagged simplex is its graded
coboundary on that simplex. -/
theorem lc_tagEvalG_tagBd (φ : ∀ n : ℕ, singularCochainGroup K X n) (τ : TagSimp X) :
    Finsupp.linearCombination K (tagEvalG K φ) (tagBd K X τ) = tagEvalG K (gCoboundary K X φ) τ := by
  obtain ⟨_ | n, σ⟩ := τ
  · rw [tagBd_zero, map_zero]
    exact (cochainEval_zero 0 σ).symm
  · have hR : tagEvalG K (gCoboundary K X φ) (⟨n + 1, σ⟩ : TagSimp X)
        = ∑ i : Fin (n + 2), (-1 : K) ^ (i : ℕ) * cochainEval n (φ n) (faceSimplex X n i σ) :=
      cochainCoboundary_eval K X n (φ n) σ
    rw [hR, tagBd_succ_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, Finsupp.linearCombination_single, one_smul, zsmul_eq_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one]
    rfl

/-- **Leibniz at a simplex.** -/
theorem tagEvalG_gCoboundary_gCupFun (φ ψ : ∀ n : ℕ, singularCochainGroup K X n) (τ : TagSimp X) :
    tagEvalG K (gCoboundary K X (gCupFun K φ ψ)) τ
      = tagEvalG K (gCupFun K (gCoboundary K X φ) ψ) τ
        + tagEvalG K (gCupFun K (gSign K φ) (gCoboundary K X ψ)) τ := by
  obtain ⟨_ | n, σ⟩ := τ
  · have h0 : tagEvalG K (gCoboundary K X (gCupFun K φ ψ)) (⟨0, σ⟩ : TagSimp X) = 0 :=
      cochainEval_zero 0 σ
    rw [h0, tagEvalG_gCupFun_range, tagEvalG_gCupFun_range, Finset.sum_range_one,
      Finset.sum_range_one]
    have h1 : tagEvalG K (gCoboundary K X φ) (TopPow.awFront (⟨0, σ⟩ : TagSimp X) 0) = 0 :=
      cochainEval_zero 0 _
    have h2 : tagEvalG K (gCoboundary K X ψ) (TopPow.awBack (⟨0, σ⟩ : TagSimp X) 0) = 0 :=
      cochainEval_zero 0 _
    rw [h1, h2, zero_mul, mul_zero, add_zero]
  · have hL : tagEvalG K (gCoboundary K X (gCupFun K φ ψ)) (⟨n + 1, σ⟩ : TagSimp X)
        = ∑ v ∈ Finset.range (n + 2), (-1 : K) ^ v *
            ∑ m ∈ Finset.range ((TopPow.vtx σ n (TopPow.succAb v) (TopPow.succAb_mono v)).1 + 1),
              tagEvalG K φ (TopPow.awFront (TopPow.vtx σ n (TopPow.succAb v) (TopPow.succAb_mono v)) m)
                * tagEvalG K ψ
                    (TopPow.awBack (TopPow.vtx σ n (TopPow.succAb v) (TopPow.succAb_mono v)) m) := by
      rw [← lc_tagEvalG_tagBd, TopPow.tagBd_eq_sum, map_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [map_smul, Finsupp.linearCombination_single, one_smul, smul_eq_mul,
        tagEvalG_gCupFun_range]
    have hR : tagEvalG K (gCupFun K (gCoboundary K X φ) ψ) (⟨n + 1, σ⟩ : TagSimp X)
          + tagEvalG K (gCupFun K (gSign K φ) (gCoboundary K X ψ)) (⟨n + 1, σ⟩ : TagSimp X)
        = ∑ i ∈ Finset.range ((⟨n + 1, σ⟩ : TagSimp X).1 + 1),
            (tagEvalG K (gCoboundary K X φ) (TopPow.awFront (⟨n + 1, σ⟩ : TagSimp X) i)
                * tagEvalG K ψ (TopPow.awBack (⟨n + 1, σ⟩ : TagSimp X) i)
              + (-1 : K) ^ i * (tagEvalG K φ (TopPow.awFront (⟨n + 1, σ⟩ : TagSimp X) i)
                * tagEvalG K (gCoboundary K X ψ) (TopPow.awBack (⟨n + 1, σ⟩ : TagSimp X) i))) := by
      rw [tagEvalG_gCupFun_range, tagEvalG_gCupFun_range, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [tagEvalG_gSign, mul_assoc]
      rfl
    have key := TopPow.binary_aw K ((LinearMap.mul K K).compl₁₂
      (Finsupp.linearCombination K (tagEvalG K φ)) (Finsupp.linearCombination K (tagEvalG K ψ))) n σ
    simp only [LinearMap.compl₁₂_apply, LinearMap.mul_apply', Finsupp.linearCombination_single,
      one_smul, lc_tagEvalG_tagBd, smul_eq_mul] at key
    rw [hL, hR]
    exact key.symm

/-- **The Leibniz formula for the graded cup.** -/
theorem gCoboundary_gCupFun (φ ψ : ∀ n : ℕ, singularCochainGroup K X n) :
    gCoboundary K X (gCupFun K φ ψ)
      = gCupFun K (gCoboundary K X φ) ψ + gCupFun K (gSign K φ) (gCoboundary K X ψ) := by
  funext n
  apply cochain_ext
  intro σ
  rw [Pi.add_apply, cochainEval_add]
  exact tagEvalG_gCoboundary_gCupFun K φ ψ ⟨n, σ⟩

end Cup

/-! ## 3. Interleaving -/

section Interleave

/-- **Interleave two families**: slot `2j` from `u j`, slot `2j + 1` from `v j`. -/
def tupInterleave {α : Type*} (r : ℕ) (u v : Fin r → α) : Fin (2 * r) → α :=
  fun m => if m.val % 2 = 0 then u ⟨m.val / 2, by have := m.isLt; omega⟩
    else v ⟨m.val / 2, by have := m.isLt; omega⟩

/-- The slot `2j + b` of the `2r`-fold power. -/
def awSlot (r : ℕ) : Fin r × Fin 2 ≃ Fin (2 * r) where
  toFun x := ⟨2 * x.1.val + x.2.val, by have := x.1.isLt; have := x.2.isLt; omega⟩
  invFun m := (⟨m.val / 2, by have := m.isLt; omega⟩, ⟨m.val % 2, by omega⟩)
  left_inv x := by
    obtain ⟨⟨j, hj⟩, ⟨b, hb⟩⟩ := x
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · show (2 * j + b) / 2 = j
      omega
    · show (2 * j + b) % 2 = b
      omega
  right_inv m := by
    obtain ⟨m, hm⟩ := m
    refine Fin.ext ?_
    show 2 * (m / 2) + m % 2 = m
    omega

theorem awSlot_val {r : ℕ} (x : Fin r × Fin 2) : (awSlot r x).val = 2 * x.1.val + x.2.val := rfl

theorem tupInterleave_even {α : Type*} {r : ℕ} (u v : Fin r → α) (j : Fin r) :
    tupInterleave r u v (awSlot r (j, 0)) = u j := by
  have h1 : (awSlot r (j, 0)).val % 2 = 0 := by
    show (2 * j.val + 0) % 2 = 0
    omega
  simp only [tupInterleave, h1, ↓reduceIte]
  exact congrArg u (Fin.ext (by show (2 * j.val + 0) / 2 = j.val; omega))

theorem tupInterleave_odd {α : Type*} {r : ℕ} (u v : Fin r → α) (j : Fin r) :
    tupInterleave r u v (awSlot r (j, 1)) = v j := by
  have h1 : ¬ ((awSlot r (j, 1)).val % 2 = 0) := by
    show ¬ ((2 * j.val + 1) % 2 = 0)
    omega
  simp only [tupInterleave, h1, ↓reduceIte]
  exact congrArg v (Fin.ext (by show (2 * j.val + 1) / 2 = j.val; omega))

/-- **Every family on `2r` slots is interleaved from its even and odd slots.** -/
theorem tupInterleave_eta {α : Type*} {r : ℕ} (Φ : Fin (2 * r) → α) :
    tupInterleave r (fun j => Φ (awSlot r (j, 0))) (fun j => Φ (awSlot r (j, 1))) = Φ := by
  funext m
  have hm := m.isLt
  simp only [tupInterleave]
  split_ifs with h
  · exact congrArg Φ (Fin.ext (by show 2 * (m.val / 2) + 0 = m.val; omega))
  · exact congrArg Φ (Fin.ext (by show 2 * (m.val / 2) + 1 = m.val; omega))

/-- A product over `2r` slots is a product over the `r` pairs. -/
theorem prod_awSlot {M : Type*} [CommMonoid M] {r : ℕ} (F : Fin (2 * r) → M) :
    ∏ s, F s = ∏ j : Fin r, (F (awSlot r (j, 0)) * F (awSlot r (j, 1))) := by
  rw [← Equiv.prod_comp (awSlot r) F, Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun j _ => Fin.prod_univ_two (fun b => F (awSlot r (j, b)))

/-- A sum over `2r` slots is a sum over the `r` pairs. -/
theorem sum_awSlot {M : Type*} [AddCommMonoid M] {r : ℕ} (F : Fin (2 * r) → M) :
    ∑ s, F s = ∑ j : Fin r, (F (awSlot r (j, 0)) + F (awSlot r (j, 1))) := by
  rw [← Equiv.sum_comp (awSlot r) F, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun j _ => Fin.sum_univ_two (fun b => F (awSlot r (j, b)))

end Interleave

/-! ## 4. The slotwise map and its evaluation -/

section SlotwiseAW

variable {X : TopCat.{0}}

/-- The cut vectors of a tuple: a cut `c j ≤ deg (t j)` in every slot. -/
abbrev awCuts {r : ℕ} (t : TupAll X r) : Finset (Fin r → ℕ) :=
  Fintype.piFinset fun j => Finset.range ((t j).1 + 1)

/-- The interleaved tuple of one cut vector. -/
def awTupOf {r : ℕ} (t : TupAll X r) (c : Fin r → ℕ) : TupAll X (2 * r) :=
  tupInterleave r (fun j => TopPow.awFront (t j) (c j)) (fun j => TopPow.awBack (t j) (c j))

theorem awTupOf_even {r : ℕ} (t : TupAll X r) (c : Fin r → ℕ) (j : Fin r) :
    awTupOf t c (awSlot r (j, 0)) = TopPow.awFront (t j) (c j) :=
  tupInterleave_even _ _ j

theorem awTupOf_odd {r : ℕ} (t : TupAll X r) (c : Fin r → ℕ) (j : Fin r) :
    awTupOf t c (awSlot r (j, 1)) = TopPow.awBack (t j) (c j) :=
  tupInterleave_odd _ _ j

/-- On a cut vector, the image tuple has the total degree of the source tuple. -/
theorem sum_awTupOf {r : ℕ} (t : TupAll X r) {c : Fin r → ℕ} (hc : c ∈ awCuts t) :
    ∑ s, (awTupOf t c s).1 = ∑ j, (t j).1 := by
  rw [sum_awSlot]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [awTupOf_even, awTupOf_odd]
  have hj : c j < (t j).1 + 1 := Finset.mem_range.mp (Fintype.mem_piFinset.mp hc j)
  show c j + ((t j).1 - c j) = (t j).1
  omega

variable (K : Type) [CommRing K] (X)

/-- **The slotwise Alexander–Whitney map** on the full model. -/
def awTupAll (r : ℕ) : tupAllMod K X r →ₗ[K] tupAllMod K X (2 * r) :=
  Finsupp.linearCombination K fun t : TupAll X r =>
    ∑ c ∈ awCuts t, Finsupp.single (awTupOf t c) (1 : K)

theorem awTupAll_single {r : ℕ} (t : TupAll X r) :
    awTupAll K X r (Finsupp.single t (1 : K)) = ∑ c ∈ awCuts t, Finsupp.single (awTupOf t c) (1 : K) := by
  rw [awTupAll, Finsupp.linearCombination_single, one_smul]

theorem tupEvalAll_awTupAll_single {r : ℕ} (φ ψ : Fin r → ∀ n : ℕ, singularCochainGroup K X n)
    (t : TupAll X r) :
    tupEvalAll K X (2 * r) (tupInterleave r φ ψ) (awTupAll K X r (Finsupp.single t (1 : K)))
      = ∏ j, tagEvalG K (gCupFun K (φ j) (ψ j)) (t j) := by
  have hterm : ∀ c : Fin r → ℕ,
      tupEvalAll K X (2 * r) (tupInterleave r φ ψ) (Finsupp.single (awTupOf t c) (1 : K))
        = ∏ j, (tagEvalG K (φ j) (TopPow.awFront (t j) (c j))
            * tagEvalG K (ψ j) (TopPow.awBack (t j) (c j))) := by
    intro c
    rw [tupEvalAll_single, prod_awSlot]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [tupInterleave_even, tupInterleave_odd, awTupOf_even, awTupOf_odd]
  rw [awTupAll_single, map_sum, Finset.sum_congr rfl fun c _ => hterm c]
  refine (Finset.prod_univ_sum (fun j => Finset.range ((t j).1 + 1))
    (fun j m => tagEvalG K (φ j) (TopPow.awFront (t j) m)
      * tagEvalG K (ψ j) (TopPow.awBack (t j) m))).symm.trans ?_
  exact Finset.prod_congr rfl fun j _ => (tagEvalG_gCupFun_range K (φ j) (ψ j) (t j)).symm

/-- **Evaluating interleaved cochains on the image is evaluating the slotwise cups.** -/
theorem tupEvalAll_awTupAll (r : ℕ) (φ ψ : Fin r → ∀ n : ℕ, singularCochainGroup K X n)
    (x : tupAllMod K X r) :
    tupEvalAll K X (2 * r) (tupInterleave r φ ψ) (awTupAll K X r x)
      = tupEvalAll K X r (fun j => gCupFun K (φ j) (ψ j)) x := by
  have h : (tupEvalAll K X (2 * r) (tupInterleave r φ ψ)).comp (awTupAll K X r)
      = tupEvalAll K X r (fun j => gCupFun K (φ j) (ψ j)) := by
    apply Finsupp.lhom_ext'
    intro t
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [tupEvalAll_awTupAll_single, tupEvalAll_single]
  exact LinearMap.congr_fun h x

end SlotwiseAW

/-! ## 5. Prefix sums over the pairs -/

section Prefix

/-- A `Fin r`-indexed family of naturals, extended by `0` past the arity. -/
def awFinExt {r : ℕ} (f : Fin r → ℕ) (l : ℕ) : ℕ := if h : l < r then f ⟨l, h⟩ else 0

theorem sum_Iio_eq_sum_range_awFinExt {r : ℕ} (f : Fin r → ℕ) (j : Fin r) :
    ∑ l ∈ Finset.Iio j, f l = ∑ l ∈ Finset.range j.val, awFinExt f l := by
  have hmap : (Finset.Iio j).map Fin.valEmbedding = Finset.range j.val := by
    rw [Fin.map_valEmbedding_Iio, Nat.Iio_eq_range]
  rw [← hmap, Finset.sum_map]
  refine Finset.sum_congr rfl fun l _ => ?_
  show f l = if h : l.val < r then f ⟨l.val, h⟩ else 0
  rw [dif_pos l.isLt]

theorem sum_range_two_mul (g : ℕ → ℕ) (j : ℕ) :
    ∑ m ∈ Finset.range (2 * j), g m = ∑ l ∈ Finset.range j, (g (2 * l) + g (2 * l + 1)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

/-- The Koszul prefix of an even slot is the prefix of the pairs below. -/
theorem prefix_awSlot_even {r : ℕ} (d : Fin (2 * r) → ℕ) (j : Fin r) :
    ∑ l ∈ Finset.Iio (awSlot r (j, 0)), d l
      = ∑ l ∈ Finset.Iio j, (d (awSlot r (l, 0)) + d (awSlot r (l, 1))) := by
  rw [sum_Iio_eq_sum_range_awFinExt, sum_Iio_eq_sum_range_awFinExt]
  show ∑ m ∈ Finset.range (2 * j.val + 0), awFinExt d m = _
  rw [add_zero, sum_range_two_mul]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l < j.val := Finset.mem_range.mp hl
  have hr : l < r := lt_trans hl' j.isLt
  simp only [awFinExt, dif_pos hr, dif_pos (show 2 * l < 2 * r by omega),
    dif_pos (show 2 * l + 1 < 2 * r by omega)]
  rfl

/-- The Koszul prefix of an odd slot adds the degree of its even partner. -/
theorem prefix_awSlot_odd {r : ℕ} (d : Fin (2 * r) → ℕ) (j : Fin r) :
    ∑ l ∈ Finset.Iio (awSlot r (j, 1)), d l
      = ∑ l ∈ Finset.Iio j, (d (awSlot r (l, 0)) + d (awSlot r (l, 1))) + d (awSlot r (j, 0)) := by
  rw [← prefix_awSlot_even, sum_Iio_eq_sum_range_awFinExt, sum_Iio_eq_sum_range_awFinExt]
  show ∑ m ∈ Finset.range (2 * j.val + 1), awFinExt d m
    = ∑ m ∈ Finset.range (2 * j.val + 0), awFinExt d m + d (awSlot r (j, 0))
  rw [Finset.sum_range_succ, add_zero]
  have hr : 2 * j.val < 2 * r := by have := j.isLt; omega
  congr 1
  show (if h : 2 * j.val < 2 * r then d ⟨2 * j.val, h⟩ else 0) = d (awSlot r (j, 0))
  rw [dif_pos hr]
  rfl

end Prefix

/-! ## 6. The chain-map law -/

section ChainMap

variable (K : Type) [CommRing K] (X : TopCat.{0})

/-- **Linearity of the evaluation in one slot**, from a pointwise identity of slot values. -/
theorem tupEvalAll_update_eq_add_smul {r : ℕ} (χ : Fin r → ∀ n : ℕ, singularCochainGroup K X n)
    (j : Fin r) (A B C : ∀ n : ℕ, singularCochainGroup K X n) (c : K)
    (h : ∀ τ, tagEvalG K A τ = tagEvalG K B τ + c * tagEvalG K C τ) (x : tupAllMod K X r) :
    tupEvalAll K X r (Function.update χ j A) x
      = tupEvalAll K X r (Function.update χ j B) x + c * tupEvalAll K X r (Function.update χ j C) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, mul_zero, add_zero]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]
    ring
  | single t a =>
    rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, tupEvalAll_single, tupEvalAll_single, tupEvalAll_single]
    have split : ∀ D : ∀ n : ℕ, singularCochainGroup K X n,
        ∏ l, tagEvalG K (Function.update χ j D l) (t l)
          = tagEvalG K D (t j) * ∏ l ∈ Finset.univ.erase j, tagEvalG K (χ l) (t l) := fun D =>
      oddPEval_prod_split (fun l => tagEvalG K (Function.update χ j D l) (t l))
        (fun l => tagEvalG K (χ l) (t l)) j (tagEvalG K D (t j))
        (congrArg (fun ψ => tagEvalG K ψ (t j)) (Function.update_self j _ χ))
        (fun l hl => congrArg (fun ψ => tagEvalG K ψ (t l)) (Function.update_of_ne hl _ χ))
    rw [split A, split B, split C, h]
    ring

variable {K X}

theorem tagEvalG_gCupFun_gSign_of_homog (φ ψ : ∀ n : ℕ, singularCochainGroup K X n) {a : ℕ}
    (hφ : ∀ m, m ≠ a → φ m = 0) (τ : TagSimp X) :
    tagEvalG K (gCupFun K (gSign K φ) ψ) τ = (-1 : K) ^ a * tagEvalG K (gCupFun K φ ψ) τ := by
  rw [tagEvalG_gCupFun_range, tagEvalG_gCupFun_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [tagEvalG_gSign, ← mul_assoc]
  by_cases hm : (TopPow.awFront τ m).1 = a
  · rw [hm]
  · rw [tagEvalG_of_eq_zero K φ _ (hφ _ hm)]
    simp only [mul_zero, zero_mul]

/-- **Leibniz at a simplex, for a homogeneous left factor.** -/
theorem tagEvalG_gCoboundary_gCupFun_of_homog (φ ψ : ∀ n : ℕ, singularCochainGroup K X n) {a : ℕ}
    (hφ : ∀ m, m ≠ a → φ m = 0) (τ : TagSimp X) :
    tagEvalG K (gCoboundary K X (gCupFun K φ ψ)) τ
      = tagEvalG K (gCupFun K (gCoboundary K X φ) ψ) τ
        + (-1 : K) ^ a * tagEvalG K (gCupFun K φ (gCoboundary K X ψ)) τ := by
  rw [tagEvalG_gCoboundary_gCupFun, tagEvalG_gCupFun_gSign_of_homog φ _ hφ]

theorem gCupFun_update_even {r : ℕ} (Φ : Fin (2 * r) → ∀ n : ℕ, singularCochainGroup K X n)
    (j : Fin r) (A : ∀ n : ℕ, singularCochainGroup K X n) :
    (fun j' => gCupFun K (Function.update Φ (awSlot r (j, 0)) A (awSlot r (j', 0)))
        (Function.update Φ (awSlot r (j, 0)) A (awSlot r (j', 1))))
      = Function.update (fun j' => gCupFun K (Φ (awSlot r (j', 0))) (Φ (awSlot r (j', 1)))) j
          (gCupFun K A (Φ (awSlot r (j, 1)))) := by
  funext j'
  by_cases hj : j' = j
  · subst hj
    have h10 : awSlot r (j', 1) ≠ awSlot r (j', 0) := fun h =>
      absurd (congrArg Prod.snd ((awSlot r).injective h)) (by decide)
    rw [Function.update_self, Function.update_of_ne h10, Function.update_self]
  · have h0 : awSlot r (j', 0) ≠ awSlot r (j, 0) := fun h =>
      hj (congrArg Prod.fst ((awSlot r).injective h))
    have h1 : awSlot r (j', 1) ≠ awSlot r (j, 0) := fun h =>
      hj (congrArg Prod.fst ((awSlot r).injective h))
    rw [Function.update_of_ne hj, Function.update_of_ne h0, Function.update_of_ne h1]

theorem gCupFun_update_odd {r : ℕ} (Φ : Fin (2 * r) → ∀ n : ℕ, singularCochainGroup K X n)
    (j : Fin r) (A : ∀ n : ℕ, singularCochainGroup K X n) :
    (fun j' => gCupFun K (Function.update Φ (awSlot r (j, 1)) A (awSlot r (j', 0)))
        (Function.update Φ (awSlot r (j, 1)) A (awSlot r (j', 1))))
      = Function.update (fun j' => gCupFun K (Φ (awSlot r (j', 0))) (Φ (awSlot r (j', 1)))) j
          (gCupFun K (Φ (awSlot r (j, 0))) A) := by
  funext j'
  by_cases hj : j' = j
  · subst hj
    have h01 : awSlot r (j', 0) ≠ awSlot r (j', 1) := fun h =>
      absurd (congrArg Prod.snd ((awSlot r).injective h)) (by decide)
    rw [Function.update_of_ne h01, Function.update_self, Function.update_self]
  · have h0 : awSlot r (j', 0) ≠ awSlot r (j, 1) := fun h =>
      hj (congrArg Prod.fst ((awSlot r).injective h))
    have h1 : awSlot r (j', 1) ≠ awSlot r (j, 1) := fun h =>
      hj (congrArg Prod.fst ((awSlot r).injective h))
    rw [Function.update_of_ne hj, Function.update_of_ne h0, Function.update_of_ne h1]

variable (K X)

/-- Evaluation on the image, for an arbitrary functional on `2r` slots. -/
theorem tupEvalAll_awTupAll' {r : ℕ} (Ψ : Fin (2 * r) → ∀ n : ℕ, singularCochainGroup K X n)
    (y : tupAllMod K X r) :
    tupEvalAll K X (2 * r) Ψ (awTupAll K X r y)
      = tupEvalAll K X r (fun j => gCupFun K (Ψ (awSlot r (j, 0))) (Ψ (awSlot r (j, 1)))) y := by
  have h := tupEvalAll_awTupAll K X r (fun j => Ψ (awSlot r (j, 0))) (fun j => Ψ (awSlot r (j, 1))) y
  rw [tupInterleave_eta] at h
  exact h

/-- **The slotwise Alexander–Whitney map is a chain map.** -/
theorem tupDAll_awTupAll (r : ℕ) (x : tupAllMod K X r) :
    tupDAll K X (2 * r) (awTupAll K X r x) = awTupAll K X r (tupDAll K X r x) := by
  refine tupAllMod_eq_of_eval K fun d Φ hΦ => ?_
  have hχ : IsHomogFun K (fun j => gCupFun K (Φ (awSlot r (j, 0))) (Φ (awSlot r (j, 1))))
      (fun j => d (awSlot r (j, 0)) + d (awSlot r (j, 1))) :=
    fun j n hn => gCupFun_of_ne K _ _ (hΦ _) (hΦ _) hn
  rw [tupEvalAll_tupDAll K Φ d hΦ, tupEvalAll_awTupAll' K X Φ (tupDAll K X r x),
    tupEvalAll_tupDAll K _ _ hχ, sum_awSlot]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tupEvalAll_awTupAll', tupEvalAll_awTupAll', gCupFun_update_even, gCupFun_update_odd,
    prefix_awSlot_even, prefix_awSlot_odd,
    tupEvalAll_update_eq_add_smul K X _ j _ _ _ ((-1 : K) ^ d (awSlot r (j, 0)))
      (tagEvalG_gCoboundary_gCupFun_of_homog (Φ (awSlot r (j, 0))) (Φ (awSlot r (j, 1))) (hΦ _))]
  ring

end ChainMap

-- PIECE 3

end

end GroupApproximation.CharClass
