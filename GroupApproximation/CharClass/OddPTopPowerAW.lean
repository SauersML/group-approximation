import GroupApproximation.CharClass.OddPTupleFunctor
import Mathlib.Algebra.BigOperators.Intervals
import GroupApproximation.Meta.AxiomGuard

/-!
# The iterated Alexander–Whitney diagonal on the flat tuple model

`awAll K X r τ` is the `r`-fold Alexander–Whitney diagonal of a tagged simplex `τ`, as an element
of the full model `tupAllMod K X r` of `OddPTupleD.lean`: the sum over the cut sequences
`0 = i₀ ≤ i₁ ≤ ⋯ ≤ i_r = deg τ` of the tuple of faces `τ[i₀..i₁], …, τ[i_{r−1}..i_r]`, with no
sign.  It is built left-nested,

    AW^{(r+1)}(σ) = Σ_i AW^{(r)}(σ[0..i]) ⊗ σ[i..k],

so that its evaluation against a tuple of cochains is the vendored left-nested cup power.

This file is the first half: sub-simplices, faces, the concatenation law, the definition and its
degree.  The chain-map law is `OddPTopPowerAWChain.lean`.

## Design

* **Sub-simplices by clamped vertex maps.**  Every face that occurs is `vtx σ a v`: the
  `a`-simplex of `σ` on the vertices `min (v 0) k, …, min (v a) k`.  The degree `a` is data and
  the clamp keeps the morphism well typed for every `v`, so no degree is ever cast.  Two
  sub-simplices are compared by `vtx_congr` (equal degrees, equal clamped vertices) and composed
  by `vtx_vtx`; a face of a sub-simplex is again a sub-simplex (`tagBd_vtx`).
* **The concatenation law.**  Appending a last slot, `d (x ⊗ τ) = d x ⊗ τ + (−1)^{deg x} x ⊗ ∂τ`
  for `x` concentrated in one total degree (`tupDAll_catLin_of_mem`): the last slot's Koszul prefix
  is the total degree of the others.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Simplicial
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

namespace TopPow

/-! ## 1. Clamped vertex maps and sub-simplices -/

/-- The vertex map `j ↦ min (v j) k` on `a + 1` vertices, as a morphism `⦋a⦌ ⟶ ⦋k⦌`. -/
def clampHom (a k : ℕ) (v : ℕ → ℕ) (hv : Monotone v) : (⦋a⦌ : SimplexCategory) ⟶ ⦋k⦌ :=
  SimplexCategory.mkHom
    ⟨fun j => ⟨min (v j.val) k, Nat.lt_succ_of_le (min_le_right _ _)⟩, fun x y hxy => by
      have h := hv (Fin.le_iff_val_le_val.mp hxy)
      show min (v x.val) k ≤ min (v y.val) k
      omega⟩

@[simp] theorem clampHom_apply (a k : ℕ) (v : ℕ → ℕ) (hv : Monotone v) (j : Fin (a + 1)) :
    ((clampHom a k v hv).toOrderHom j : ℕ) = min (v j.val) k :=
  rfl

section Faces

variable {X : TopCat.{0}}

/-- **The sub-simplex of `σ` on the clamped vertices** `min (v 0) k, …, min (v a) k`, tagged with
its degree `a`. -/
def vtx {k : ℕ} (σ : singularSimplices X k) (a : ℕ) (v : ℕ → ℕ) (hv : Monotone v) : TagSimp X :=
  ⟨a, (TopCat.toSSet.obj X).map (clampHom a k v hv).op σ⟩

@[simp] theorem vtx_fst {k : ℕ} (σ : singularSimplices X k) (a : ℕ) (v : ℕ → ℕ)
    (hv : Monotone v) : (vtx σ a v hv).1 = a :=
  rfl

/-- **Two sub-simplices agree** when their degrees agree and their clamped vertices agree. -/
theorem vtx_congr {k : ℕ} (σ : singularSimplices X k) {a a' : ℕ} {v v' : ℕ → ℕ}
    (hv : Monotone v) (hv' : Monotone v') (ha : a = a')
    (hvv : ∀ j, j ≤ a → min (v j) k = min (v' j) k) :
    vtx σ a v hv = vtx σ a' v' hv' := by
  subst ha
  have hf : clampHom a k v hv = clampHom a k v' hv' := by
    ext j : 3
    apply Fin.ext
    rw [clampHom_apply, clampHom_apply]
    exact hvv j.val (Nat.le_of_lt_succ j.isLt)
  unfold vtx
  rw [hf]

/-- **A sub-simplex of a sub-simplex is a sub-simplex**, on the composed vertex map, as soon as the
inner map stays below the outer degree. -/
theorem vtx_vtx {k : ℕ} (σ : singularSimplices X k) (a : ℕ) {v : ℕ → ℕ} (hv : Monotone v)
    (b : ℕ) {w : ℕ → ℕ} (hw : Monotone w) (hwb : ∀ j, j ≤ b → w j ≤ a) :
    vtx (vtx σ a v hv).2 b w hw = vtx σ b (v ∘ w) (hv.comp hw) := by
  have hcomp : clampHom b a w hw ≫ clampHom a k v hv = clampHom b k (v ∘ w) (hv.comp hw) := by
    ext j : 3
    apply Fin.ext
    show min (v (min (w j.val) a)) k = min (v (w j.val)) k
    rw [min_eq_left (hwb j.val (Nat.le_of_lt_succ j.isLt))]
  show (⟨b, (TopCat.toSSet.obj X).map (clampHom b a w hw).op
      ((TopCat.toSSet.obj X).map (clampHom a k v hv).op σ)⟩ : TagSimp X)
    = ⟨b, (TopCat.toSSet.obj X).map (clampHom b k (v ∘ w) (hv.comp hw)).op σ⟩
  rw [← Functor.map_comp_apply, ← op_comp, hcomp]

/-! ## 2. Faces -/

/-- Skip vertex `l`: the vertex map of the `l`-th face. -/
def succAb (l j : ℕ) : ℕ := if j < l then j else j + 1

theorem succAb_mono (l : ℕ) : Monotone (succAb l) := by
  intro x y hxy
  simp only [succAb]
  split_ifs <;> omega

theorem succAb_le (l j : ℕ) : succAb l j ≤ j + 1 := by
  simp only [succAb]
  split_ifs <;> omega

/-- The `i`-th face of a singular `(n+1)`-simplex is the sub-simplex skipping vertex `i`. -/
theorem faceSimplex_eq_vtx (n : ℕ) (i : Fin (n + 2)) (σ : singularSimplices X (n + 1)) :
    (⟨n, faceSimplex X n i σ⟩ : TagSimp X) = vtx σ n (succAb i.val) (succAb_mono _) := by
  have hδ : SimplexCategory.δ i = clampHom n (n + 1) (succAb i.val) (succAb_mono _) := by
    ext j : 3
    apply Fin.ext
    rw [clampHom_apply]
    show (i.succAbove j : ℕ) = min (succAb i.val j.val) (n + 1)
    have hj1 : j.val < n + 1 := j.isLt
    by_cases hj : j.val < i.val
    · have hlt : Fin.castSucc j < i := by
        rw [Fin.lt_def, Fin.val_castSucc]
        exact hj
      rw [Fin.succAbove_of_castSucc_lt i j hlt, Fin.val_castSucc]
      simp only [succAb, if_pos hj]
      rw [min_eq_left (show j.val ≤ n + 1 by omega)]
    · have hle : i ≤ Fin.castSucc j := by
        rw [Fin.le_iff_val_le_val, Fin.val_castSucc]
        omega
      rw [Fin.succAbove_of_le_castSucc i j hle, Fin.val_succ]
      simp only [succAb, if_neg hj]
      rw [min_eq_left (show j.val + 1 ≤ n + 1 by omega)]
  show (⟨n, (TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ⟩ : TagSimp X) = _
  rw [hδ]
  rfl

/-- **The boundary of a tagged simplex of positive degree, as a sum of sub-simplices.** -/
theorem tagBd_eq_sum (K : Type) [CommRing K] (n : ℕ) (σ : singularSimplices X (n + 1)) :
    tagBd K X ⟨n + 1, σ⟩
      = ∑ l ∈ Finset.range (n + 1 + 1),
          ((-1 : K) ^ l) • Finsupp.single (vtx σ n (succAb l) (succAb_mono l)) (1 : K) := by
  rw [tagBd_succ_eq_sum]
  have h : ∀ i : Fin (n + 2),
      ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (⟨n, faceSimplex X n i σ⟩ : TagSimp X) (1 : K)
        = ((-1 : K) ^ (i : ℕ)) •
            Finsupp.single (vtx σ n (succAb (i : ℕ)) (succAb_mono (i : ℕ))) (1 : K) := fun i => by
    rw [faceSimplex_eq_vtx n i σ, ← Int.cast_smul_eq_zsmul K, Int.cast_pow, Int.cast_neg,
      Int.cast_one]
  rw [Finset.sum_congr rfl fun i _ => h i]
  exact Fin.sum_univ_eq_sum_range
    (fun l => ((-1 : K) ^ l) • Finsupp.single (vtx σ n (succAb l) (succAb_mono l)) (1 : K)) (n + 2)

/-- **The boundary of a sub-simplex of positive degree** is the sum of the sub-simplices on the
composed face maps. -/
theorem tagBd_vtx (K : Type) [CommRing K] {k : ℕ} (σ : singularSimplices X k) (a : ℕ) {v : ℕ → ℕ}
    (hv : Monotone v) :
    tagBd K X (vtx σ (a + 1) v hv)
      = ∑ l ∈ Finset.range (a + 1 + 1),
          ((-1 : K) ^ l) • Finsupp.single (vtx σ a (v ∘ succAb l) (hv.comp (succAb_mono l))) (1 : K) := by
  have h := tagBd_eq_sum K a (vtx σ (a + 1) v hv).2
  refine h.trans (Finset.sum_congr rfl fun l _ => ?_)
  exact congrArg (fun τ => ((-1 : K) ^ l) • Finsupp.single τ (1 : K))
    (vtx_vtx σ (a + 1) hv a (succAb_mono l) fun j hj => by
      have := succAb_le l j
      omega)

/-- A sub-simplex of degree `0` has no boundary. -/
theorem tagBd_vtx_zero (K : Type) [CommRing K] {k : ℕ} (σ : singularSimplices X k) (v : ℕ → ℕ)
    (hv : Monotone v) : tagBd K X (vtx σ 0 v hv) = 0 :=
  rfl

/-! ## 3. Front and back faces -/

theorem addRight_mono (i : ℕ) : Monotone fun j : ℕ => j + i :=
  fun _ _ h => Nat.add_le_add_right h i

/-- The front face `τ[0..i]`, of degree `i`. -/
def awFront (τ : TagSimp X) (i : ℕ) : TagSimp X := vtx τ.2 i id monotone_id

/-- The back face `τ[i..k]`, of degree `k − i`. -/
def awBack (τ : TagSimp X) (i : ℕ) : TagSimp X :=
  vtx τ.2 (τ.1 - i) (fun j => j + i) (addRight_mono i)

end Faces

/-! ## 4. Appending a slot -/

section Concat

variable (K : Type) [CommRing K] (X : TopCat.{0})

/-- Append a tagged simplex as the last slot. -/
def snocT {r : ℕ} (t : TupAll X r) (τ : TagSimp X) : TupAll X (r + 1) := Fin.snoc t τ

/-- **The concatenation** `x ⊗ c`: `c`'s simplices in a new last slot; bilinear. -/
def catLin (r : ℕ) : tupAllMod K X r →ₗ[K] (TagSimp X →₀ K) →ₗ[K] tupAllMod K X (r + 1) :=
  Finsupp.linearCombination K fun t =>
    Finsupp.linearCombination K fun τ => Finsupp.single (snocT X t τ) (1 : K)

theorem catLin_single_left {r : ℕ} (t : TupAll X r) (c : TagSimp X →₀ K) :
    catLin K X r (Finsupp.single t 1) c
      = Finsupp.linearCombination K (fun τ => Finsupp.single (snocT X t τ) (1 : K)) c := by
  unfold catLin
  rw [Finsupp.linearCombination_single, one_smul]

theorem catLin_single {r : ℕ} (t : TupAll X r) (τ : TagSimp X) :
    catLin K X r (Finsupp.single t 1) (Finsupp.single τ 1) = Finsupp.single (snocT X t τ) 1 := by
  rw [catLin_single_left, Finsupp.linearCombination_single, one_smul]

/-- The tuples of total degree `d`. -/
def degSetT (r d : ℕ) : Set (TupAll X r) := {t | ∑ j, (t j).1 = d}

theorem sum_snocT {r : ℕ} (t : TupAll X r) (τ : TagSimp X) :
    ∑ j, (snocT X t τ j).1 = ∑ j, (t j).1 + τ.1 := by
  rw [Fin.sum_univ_castSucc]
  unfold snocT
  rw [Fin.snoc_last]
  simp only [Fin.snoc_castSucc]

theorem tupPre_snocT_castSucc {r : ℕ} (t : TupAll X r) (τ : TagSimp X) (j : Fin r) :
    tupPre (snocT X t τ) j.castSucc = tupPre t j := by
  rw [tupPre_eq_sum_range, tupPre_eq_sum_range, Fin.val_castSucc]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlr : l < r := lt_trans (Finset.mem_range.mp hl) j.isLt
  unfold tupDeg
  rw [dif_pos hlr, dif_pos (Nat.lt_succ_of_lt hlr)]
  exact congrArg Sigma.fst (Fin.snoc_castSucc (α := fun _ => TagSimp X) τ t ⟨l, hlr⟩)

theorem tupPre_snocT_last {r : ℕ} (t : TupAll X r) (τ : TagSimp X) :
    tupPre (snocT X t τ) (Fin.last r) = ∑ j, (t j).1 := by
  rw [tupPre_eq_sum_range, Fin.val_last, tupTot_eq_sum_range]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlr : l < r := Finset.mem_range.mp hl
  unfold tupDeg
  rw [dif_pos hlr, dif_pos (Nat.lt_succ_of_lt hlr)]
  exact congrArg Sigma.fst (Fin.snoc_castSucc (α := fun _ => TagSimp X) τ t ⟨l, hlr⟩)

/-- Differentiating an earlier slot commutes with appending. -/
theorem slotBd_castSucc_snocT {r : ℕ} (t : TupAll X r) (τ : TagSimp X) (j : Fin r) :
    slotBd K X j.castSucc (Finsupp.single (snocT X t τ) 1)
      = catLin K X r (slotBd K X j (Finsupp.single t 1)) (Finsupp.single τ 1) := by
  rw [slotBd_single, slotBd_single, slotBdGen, slotBdGen, tupPre_snocT_castSucc]
  have hflip : ∀ y : tupAllMod K X r,
      catLin K X r y (Finsupp.single τ 1) = ((catLin K X r).flip (Finsupp.single τ 1)) y :=
    fun _ => rfl
  rw [hflip, map_smul, Finsupp.apply_linearCombination]
  refine congrArg (fun z => ((-1 : K) ^ tupPre t j) • z) ?_
  have ht : snocT X t τ j.castSucc = t j := Fin.snoc_castSucc (α := fun _ => TagSimp X) τ t j
  rw [ht]
  refine tupLC_congr_fun K (fun τ' => ?_) _
  show Finsupp.single (Function.update (snocT X t τ) j.castSucc τ') (1 : K)
    = catLin K X r (Finsupp.single (Function.update t j τ') 1) (Finsupp.single τ 1)
  rw [catLin_single]
  unfold snocT
  rw [Fin.snoc_update]

/-- Differentiating the appended slot. -/
theorem slotBd_last_snocT {r : ℕ} (t : TupAll X r) (τ : TagSimp X) :
    slotBd K X (Fin.last r) (Finsupp.single (snocT X t τ) 1)
      = ((-1 : K) ^ (∑ j, (t j).1)) • catLin K X r (Finsupp.single t 1) (tagBd K X τ) := by
  rw [slotBd_single, slotBdGen, tupPre_snocT_last, catLin_single_left]
  have hLC : Finsupp.linearCombination K
        (fun τ' => Finsupp.single (Function.update (snocT X t τ) (Fin.last r) τ') (1 : K))
        (tagBd K X (snocT X t τ (Fin.last r)))
      = Finsupp.linearCombination K (fun τ' => Finsupp.single (snocT X t τ') (1 : K))
          (tagBd K X τ) := by
    have hl : snocT X t τ (Fin.last r) = τ := Fin.snoc_last (α := fun _ => TagSimp X) τ t
    rw [hl]
    refine tupLC_congr_fun K (fun τ' => ?_) _
    unfold snocT
    rw [Fin.update_snoc_last]
  rw [hLC]

/-- **The concatenation law on a basis tuple.** -/
theorem tupDAll_catLin_single {r : ℕ} (t : TupAll X r) (τ : TagSimp X) :
    tupDAll K X (r + 1) (catLin K X r (Finsupp.single t 1) (Finsupp.single τ 1))
      = catLin K X r (tupDAll K X r (Finsupp.single t 1)) (Finsupp.single τ 1)
        + ((-1 : K) ^ (∑ j, (t j).1)) • catLin K X r (Finsupp.single t 1) (tagBd K X τ) := by
  rw [catLin_single, tupDAll, LinearMap.sum_apply, Fin.sum_univ_castSucc, slotBd_last_snocT]
  refine congrArg (· + _) ?_
  rw [tupDAll, LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => slotBd_castSucc_snocT K X t τ j

/-- Two linear maps agreeing on the basis tuples of a set agree on everything supported there. -/
theorem eq_on_supported {M : Type} [AddCommGroup M] [Module K M] {r : ℕ}
    (L R : tupAllMod K X r →ₗ[K] M) (s : Set (TupAll X r))
    (h : ∀ t ∈ s, L (Finsupp.single t 1) = R (Finsupp.single t 1))
    {x : tupAllMod K X r} (hx : x ∈ Finsupp.supported K K s) : L x = R x := by
  have hx' := (Finsupp.mem_supported K x).mp hx
  rw [← Finsupp.sum_single x, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [← Finsupp.smul_single_one, map_smul, map_smul, h t (hx' ht)]

/-- **The concatenation law**: `d (x ⊗ τ) = d x ⊗ τ + (−1)^d x ⊗ ∂τ` for `x` of total degree `d`. -/
theorem tupDAll_catLin_of_mem {r d : ℕ} {x : tupAllMod K X r}
    (hx : x ∈ Finsupp.supported K K (degSetT X r d)) (τ : TagSimp X) :
    tupDAll K X (r + 1) (catLin K X r x (Finsupp.single τ 1))
      = catLin K X r (tupDAll K X r x) (Finsupp.single τ 1)
        + ((-1 : K) ^ d) • catLin K X r x (tagBd K X τ) := by
  have h := eq_on_supported K X
    ((tupDAll K X (r + 1)).comp ((catLin K X r).flip (Finsupp.single τ 1)))
    (((catLin K X r).flip (Finsupp.single τ 1)).comp (tupDAll K X r)
      + ((-1 : K) ^ d) • (catLin K X r).flip (tagBd K X τ))
    (degSetT X r d) (fun t ht => by
      show tupDAll K X (r + 1) (catLin K X r (Finsupp.single t 1) (Finsupp.single τ 1))
        = catLin K X r (tupDAll K X r (Finsupp.single t 1)) (Finsupp.single τ 1)
          + ((-1 : K) ^ d) • catLin K X r (Finsupp.single t 1) (tagBd K X τ)
      rw [tupDAll_catLin_single, show (∑ j, (t j).1) = d from ht]) hx
  exact h

/-- Appending a simplex of degree `e` to a tuple of total degree `d` gives total degree `d + e`. -/
theorem catLin_mem {r d : ℕ} {x : tupAllMod K X r}
    (hx : x ∈ Finsupp.supported K K (degSetT X r d)) (τ : TagSimp X) :
    catLin K X r x (Finsupp.single τ 1) ∈ Finsupp.supported K K (degSetT X (r + 1) (d + τ.1)) := by
  classical
  have h := eq_on_supported K X ((catLin K X r).flip (Finsupp.single τ 1))
    (Finsupp.lmapDomain K K fun t => snocT X t τ) (degSetT X r d) (fun t _ => by
      rw [LinearMap.flip_apply, catLin_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single])
    hx
  rw [LinearMap.flip_apply, Finsupp.lmapDomain_apply] at h
  rw [h]
  refine (Finsupp.mem_supported K _).mpr fun t' ht' => ?_
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ht')
  show (∑ j, (snocT X t τ j).1) = d + τ.1
  rw [sum_snocT, show (∑ j, (t j).1) = d from (Finsupp.mem_supported K x).mp hx ht]

end Concat

/-! ## 5. The iterated Alexander–Whitney diagonal -/

section Diagonal

variable (K : Type) [CommRing K] (X : TopCat.{0})

/-- **The `r`-fold Alexander–Whitney diagonal** of a tagged simplex, left-nested:
`AW^{(0)}(τ)` is the empty tuple when `τ` is a point and `0` otherwise, and
`AW^{(r+1)}(τ) = Σ_{i ≤ deg τ} AW^{(r)}(τ[0..i]) ⊗ τ[i..deg τ]`. -/
def awAll (r : ℕ) (τ : TagSimp X) : tupAllMod K X r :=
  match r with
  | 0 => if τ.1 = 0 then Finsupp.single (Fin.elim0 : TupAll X 0) 1 else 0
  | r + 1 => ∑ i ∈ Finset.range (τ.1 + 1),
      catLin K X r (awAll r (awFront τ i)) (Finsupp.single (awBack τ i) 1)

/-- The linear extension of the diagonal to chains. -/
def awLin (r : ℕ) : (TagSimp X →₀ K) →ₗ[K] tupAllMod K X r :=
  Finsupp.linearCombination K (awAll K X r)

theorem awLin_single (r : ℕ) (τ : TagSimp X) :
    awLin K X r (Finsupp.single τ 1) = awAll K X r τ := by
  show Finsupp.linearCombination K (awAll K X r) (Finsupp.single τ 1) = awAll K X r τ
  rw [Finsupp.linearCombination_single, one_smul]

theorem awAll_zero (τ : TagSimp X) :
    awAll K X 0 τ = if τ.1 = 0 then Finsupp.single (Fin.elim0 : TupAll X 0) 1 else 0 :=
  rfl

theorem awAll_succ (r : ℕ) (τ : TagSimp X) :
    awAll K X (r + 1) τ = ∑ i ∈ Finset.range (τ.1 + 1),
      catLin K X r (awAll K X r (awFront τ i)) (Finsupp.single (awBack τ i) 1) :=
  rfl

/-- **The diagonal of a `k`-simplex lives in total degree `k`.** -/
theorem awAll_mem (r : ℕ) (τ : TagSimp X) :
    awAll K X r τ ∈ Finsupp.supported K K (degSetT X r τ.1) := by
  induction r generalizing τ with
  | zero =>
    rw [awAll_zero]
    split_ifs with h
    · refine Finsupp.single_mem_supported K 1 ?_
      show (∑ j : Fin 0, ((Fin.elim0 : TupAll X 0) j).1) = τ.1
      rw [Fin.sum_univ_zero, h]
    · exact Submodule.zero_mem _
  | succ r ih =>
    rw [awAll_succ]
    refine Submodule.sum_mem _ fun i hi => ?_
    have hik : i ≤ τ.1 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have h := catLin_mem K X (ih (awFront τ i)) (awBack τ i)
    have hdeg : (awFront τ i).1 + (awBack τ i).1 = τ.1 := by
      show i + (τ.1 - i) = τ.1
      omega
    rw [hdeg] at h
    exact h

end Diagonal

#audit_axioms vtx_vtx
#audit_axioms tagBd_vtx
#audit_axioms tupDAll_catLin_of_mem
#audit_axioms awAll_mem

end TopPow

end

end GroupApproximation.CharClass
