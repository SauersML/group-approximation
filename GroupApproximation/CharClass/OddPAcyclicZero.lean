import GroupApproximation.CharClass.OddPAcyclic
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularH0General

/-!
# Degree zero: augmentation cycles of the flat tuple power over a standard simplex are boundaries

Lane `lix-cupone`, block `OddPAcyclic*`, export (E0) for the diagonal's `AcyclicZeroOnModels`.

## The route

* **One slot, degree zero.**  Over a path-connected space every difference of two `0`-simplices is a
  boundary of the signed `Finsupp` complex.  The vendored `H0Gen.chainGenerator_sub_mem_range` says
  this for Mathlib's coproduct complex.  The plain linear map `fromCoprod = Sigma.desc lsingle` carries
  it over, because at degrees `1 → 0` it intertwines the two differentials — checked on generators
  with the vendored signed formula `singularBoundary_sigma_ι_formula` against `singFreeR_d_single`,
  both with the alternating signs intact.  No unsigned face sum is involved.
* **One slot of a tuple.**  If every slot of `t` is a point, replacing slot `j` by a `1`-chain `w`
  and differentiating gives exactly slot `j` replaced by `∂ w`: every other slot is a point, whose
  boundary is `0`, and the prefix sign at `j` is `(-1)^0 = 1`.  So `t` and `t` with one point changed
  are homologous.
* **All slots.**  Changing the points one slot at a time (`mixIdx`) connects any two point-tuples,
  and an augmentation cycle is a combination of differences of point-tuples.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

noncomputable section

namespace OddPAcyclic

/-! ## 1. One slot, degree zero -/

section OneSlot

variable (K : Type) [CommRing K] (X : TopCat.{0})

/-- From Mathlib's coproduct carrier to the `Finsupp` carrier: `ι σ ↦ single σ 1`. -/
def fromCoprod (m : ℕ) :
    AffineBarycentricSubdivision.singularChainGroup K X m
      ⟶ ModuleCat.of K (singularSimplices X m →₀ K) :=
  Limits.Sigma.desc (fun σ => ModuleCat.ofHom (Finsupp.lsingle σ))

theorem ι_fromCoprod (m : ℕ) (σ : singularSimplices X m) :
    Limits.Sigma.ι (fun (_ : singularSimplices X m) => ModuleCat.of K K) σ ≫ fromCoprod K X m
      = ModuleCat.ofHom (Finsupp.lsingle σ) :=
  Limits.Sigma.ι_desc _ σ

theorem fromCoprod_generator (m : ℕ) (σ : singularSimplices X m) :
    (fromCoprod K X m).hom (AffineBarycentricSubdivision.chainGenerator K X m σ)
      = Finsupp.single σ (1 : K) :=
  congrArg (fun (g : ModuleCat.of K K ⟶ ModuleCat.of K (singularSimplices X m →₀ K)) =>
    g.hom (1 : K)) (ι_fromCoprod K X m σ)

/-- **`fromCoprod` intertwines the two signed differentials at degrees `1 → 0`.** -/
theorem fromCoprod_comm :
    AffineBarycentricSubdivision.singularBoundary K X 0 ≫ fromCoprod K X 0
      = fromCoprod K X 1 ≫ ModuleCat.ofHom (chainBd K X 0) := by
  apply Limits.Sigma.hom_ext
  intro γ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (fromCoprod K X 0).hom ((AffineBarycentricSubdivision.singularBoundary K X 0).hom
      (AffineBarycentricSubdivision.chainGenerator K X (0 + 1) γ))
    = (((singFreeR K).obj X).d (0 + 1) 0).hom
      ((fromCoprod K X 1).hom (AffineBarycentricSubdivision.chainGenerator K X 1 γ))
  rw [AffineBarycentricSubdivision.singularBoundary_chainGenerator_formula, fromCoprod_generator,
    singFreeR_d_single, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, fromCoprod_generator, ← Int.cast_smul_eq_zsmul K ((-1 : ℤ) ^ (i : ℕ))]
  congr 1
  push_cast
  ring

/-- **Over a path-connected space every difference of two points is a boundary.** -/
theorem single_sub_mem_range [PathConnectedSpace X] (σ τ : singularSimplices X 0) :
    Finsupp.single σ (1 : K) - Finsupp.single τ (1 : K) ∈ LinearMap.range (chainBd K X 0) := by
  obtain ⟨w, hw⟩ := H0Gen.chainGenerator_sub_mem_range (R := K) (X := X) σ τ
  refine ⟨(fromCoprod K X 1).hom w, ?_⟩
  have h := congrArg (fun φ => φ.hom w) (fromCoprod_comm K X)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h
  rw [← h, hw, map_sub, fromCoprod_generator, fromCoprod_generator]

end OneSlot

/-! ## 2. One slot of a point-tuple -/

section Tuple

variable (K : Type) [Field K] (X : TopCat.{0})

theorem tagBd_of_fst_eq_zero (τ : TagSimp X) (h : τ.1 = 0) : tagBd K X τ = 0 := by
  obtain ⟨m, σ⟩ := τ
  cases m with
  | zero => rfl
  | succ m => exact absurd h (Nat.succ_ne_zero m)

theorem tupPre_of_points {r : ℕ} (t : TupAll X r) (h0 : ∀ l, (t l).1 = 0) (j : Fin r) :
    tupPre t j = 0 := by
  show ∑ l ∈ Finset.Iio j, (t l).1 = 0
  exact Finset.sum_eq_zero fun l _ => h0 l

/-- **Differentiating a point-tuple with one slot replaced by a `1`-chain.** -/
theorem tupDAll_slotLift_points {r : ℕ} (t : TupAll X r) (h0 : ∀ l, (t l).1 = 0) (j : Fin r)
    (w : singularSimplices X 1 →₀ K) :
    tupDAll K X r (slotLift K X t j (tagAt K X 1 w))
      = slotLift K X t j (tagAt K X 0 (chainBd K X 0 w)) := by
  rw [tupDAll, LinearMap.sum_apply]
  refine (Finset.sum_eq_single j (fun l _ hlj => ?_) (fun hj => absurd (Finset.mem_univ j) hj)).trans
    ?_
  · rw [slotLift, Finsupp.apply_linearCombination]
    have hfun : ∀ τ : TagSimp X,
        (⇑(slotBd K X l) ∘ fun τ : TagSimp X => Finsupp.single (Function.update t j τ) (1 : K)) τ
          = 0 := by
      intro τ
      show slotBd K X l (Finsupp.single (Function.update t j τ) (1 : K)) = 0
      rw [slotBd_eq_slotOp, slotOp_single, Function.update_of_ne hlj,
        tagBd_of_fst_eq_zero K X (t l) (h0 l), map_zero, smul_zero]
    rw [tupLC_congr_fun K hfun]
    exact linearCombinationR_zero_fun _
  · rw [slotBd_eq_slotOp, slotOp_slotLift_same, tupPre_of_points X t h0 j, pow_zero, one_smul]
    have hb : bdLC K X (tagAt K X 1 w) = tagAt K X 0 (chainBd K X 0 w) := bdLC_tagAt_succ K X 0 w
    change slotLift K X t j (bdLC K X (tagAt K X 1 w)) = _
    rw [hb]

/-- The slot-`j` replacement of a point-tuple by a `1`-chain has total degree one. -/
theorem slotLift_tagAt_one_mem {r : ℕ} (t : TupAll X r) (h0 : ∀ l, (t l).1 = 0) (j : Fin r)
    (w : singularSimplices X 1 →₀ K) : slotLift K X t j (tagAt K X 1 w) ∈ degSub K X r 1 := by
  rw [tagAt_eq_mapDomain, slotLift, Finsupp.linearCombination_mapDomain]
  refine tupLC_mem K _ _ (fun γ => Finsupp.single_mem_supported K (1 : K) ?_) _
  show ∑ l, (Function.update t j (⟨1, γ⟩ : TagSimp X) l).1 = 1
  have hs : ∑ l, (Function.update t j (⟨1, γ⟩ : TagSimp X) l).1 + (t j).1
      = ∑ l, (t l).1 + 1 := sum_fst_update X t j ⟨1, γ⟩
  have ht : ∑ l, (t l).1 = 0 := Finset.sum_eq_zero fun l _ => h0 l
  have hj := h0 j
  omega

/-- Every slot of a degree-`0` tuple is a point. -/
theorem points_of_tupIdx_zero {r : ℕ} (t : TupIdx X r 0) (l : Fin r) : (t.1 l).1 = 0 := by
  have hle : (t.1 l).1 ≤ ∑ m, (t.1 m).1 :=
    Finset.single_le_sum (f := fun m => (t.1 m).1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  have ht : ∑ m, (t.1 m).1 = 0 := t.2
  omega

/-- **Changing one point of a point-tuple is a boundary.** -/
theorem single_sub_update_mem_range [PathConnectedSpace X] {r : ℕ} (t t' : TupIdx X r 0)
    (j : Fin r) (τ : TagSimp X) (hτ : τ.1 = 0) (ht' : t'.1 = Function.update t.1 j τ) :
    Finsupp.single t (1 : K) - Finsupp.single t' (1 : K) ∈ LinearMap.range (tupD K X r 0) := by
  have h0 := points_of_tupIdx_zero X t
  obtain ⟨m, σ'⟩ := τ
  obtain rfl : m = 0 := hτ
  obtain ⟨σ, hj⟩ : ∃ σ : singularSimplices X 0, t.1 j = ⟨0, σ⟩ := by
    have hj0 := h0 j
    revert hj0
    generalize t.1 j = τ₀
    intro hτ₀
    obtain ⟨m₀, σ⟩ := τ₀
    obtain rfl : m₀ = 0 := hτ₀
    exact ⟨σ, rfl⟩
  obtain ⟨w, hw⟩ := single_sub_mem_range K X σ σ'
  obtain ⟨z, hz⟩ := exists_tupIncl_eq K X 1 _ (slotLift_tagAt_one_mem K X t.1 h0 j w)
  refine ⟨z, tupIncl_injective K X 0 ?_⟩
  have h : tupIncl K X r 0 (tupD K X r 0 z) = tupDAll K X r (tupIncl K X r 1 z) :=
    LinearMap.congr_fun (tupIncl_comp_tupD K X 0) z
  have hupd : Function.update t.1 j (⟨0, σ⟩ : TagSimp X) = t.1 := by
    rw [← hj, Function.update_eq_self]
  rw [h, hz, tupDAll_slotLift_points K X t.1 h0 j w, hw]
  simp only [map_sub, tagAt_single, tupIncl_single, slotLift, Finsupp.linearCombination_single,
    one_smul, hupd, ht']

/-! ## 3. All slots -/

/-- The tuple taking the points of `t'` below slot `m` and those of `t` from slot `m` on. -/
def mixIdx {r : ℕ} (t t' : TupIdx X r 0) (m : ℕ) : TupIdx X r 0 :=
  ⟨fun l => if (l : ℕ) < m then t'.1 l else t.1 l,
    Finset.sum_eq_zero fun l _ => by
      show (if (l : ℕ) < m then t'.1 l else t.1 l).1 = 0
      split_ifs
      · exact points_of_tupIdx_zero X t' l
      · exact points_of_tupIdx_zero X t l⟩

theorem mixIdx_zero {r : ℕ} (t t' : TupIdx X r 0) : mixIdx X t t' 0 = t := by
  apply Subtype.ext
  funext l
  show (if (l : ℕ) < 0 then t'.1 l else t.1 l) = t.1 l
  rw [if_neg (Nat.not_lt_zero _)]

theorem mixIdx_card {r : ℕ} (t t' : TupIdx X r 0) : mixIdx X t t' r = t' := by
  apply Subtype.ext
  funext l
  show (if (l : ℕ) < r then t'.1 l else t.1 l) = t'.1 l
  rw [if_pos l.isLt]

theorem mixIdx_succ {r : ℕ} (t t' : TupIdx X r 0) (m : ℕ) (hm : m < r) :
    (mixIdx X t t' (m + 1)).1 = Function.update (mixIdx X t t' m).1 ⟨m, hm⟩ (t'.1 ⟨m, hm⟩) := by
  funext l
  by_cases hl : l = ⟨m, hm⟩
  · subst hl
    rw [Function.update_self]
    show (if m < m + 1 then t'.1 ⟨m, hm⟩ else t.1 ⟨m, hm⟩) = t'.1 ⟨m, hm⟩
    rw [if_pos (Nat.lt_succ_self m)]
  · rw [Function.update_of_ne hl]
    have hlm : (l : ℕ) ≠ m := fun h => hl (Fin.ext h)
    show (if (l : ℕ) < m + 1 then t'.1 l else t.1 l) = (if (l : ℕ) < m then t'.1 l else t.1 l)
    by_cases h1 : (l : ℕ) < m
    · rw [if_pos h1, if_pos (Nat.lt_succ_of_lt h1)]
    · rw [if_neg h1, if_neg (by omega)]

/-- **Any two point-tuples are homologous.** -/
theorem single_sub_single_mem_range [PathConnectedSpace X] {r : ℕ} (t t' : TupIdx X r 0) :
    Finsupp.single t (1 : K) - Finsupp.single t' (1 : K) ∈ LinearMap.range (tupD K X r 0) := by
  have step : ∀ m : ℕ, m ≤ r →
      Finsupp.single t (1 : K) - Finsupp.single (mixIdx X t t' m) (1 : K)
        ∈ LinearMap.range (tupD K X r 0) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [mixIdx_zero, sub_self]
      exact (LinearMap.range (tupD K X r 0)).zero_mem
    | succ m ih =>
      intro hm
      have hm' : m < r := hm
      have hdiff := single_sub_update_mem_range K X (mixIdx X t t' m) (mixIdx X t t' (m + 1))
        ⟨m, hm'⟩ (t'.1 ⟨m, hm'⟩) (points_of_tupIdx_zero X t' ⟨m, hm'⟩) (mixIdx_succ X t t' m hm')
      have hsplit : Finsupp.single t (1 : K) - Finsupp.single (mixIdx X t t' (m + 1)) (1 : K)
          = (Finsupp.single t (1 : K) - Finsupp.single (mixIdx X t t' m) (1 : K))
            + (Finsupp.single (mixIdx X t t' m) (1 : K)
              - Finsupp.single (mixIdx X t t' (m + 1)) (1 : K)) := by
        abel
      rw [hsplit]
      exact (LinearMap.range (tupD K X r 0)).add_mem (ih (Nat.le_of_succ_le hm)) hdiff
  have h := step r le_rfl
  rwa [mixIdx_card] at h

/-- **An augmentation cycle of the degree-`0` carrier is a boundary**, over a path-connected space. -/
theorem tupD_exists_preimage_zero_of_pathConnected [PathConnectedSpace X] (r : ℕ)
    (y : tupMod K X r 0) (hy : Finsupp.linearCombination K (fun _ => (1 : K)) y = 0) :
    ∃ z : tupMod K X r 1, tupD K X r 0 z = y := by
  by_cases hy0 : y = 0
  · exact ⟨0, by rw [map_zero, hy0]⟩
  obtain ⟨t₀, -⟩ := Finsupp.support_nonempty_iff.mpr hy0
  have hall : ∀ y' : tupMod K X r 0,
      y' - Finsupp.linearCombination K (fun _ => (1 : K)) y' • Finsupp.single t₀ (1 : K)
        ∈ LinearMap.range (tupD K X r 0) := by
    intro y'
    induction y' using Finsupp.induction_linear with
    | zero =>
      rw [map_zero, zero_smul, sub_zero]
      exact (LinearMap.range (tupD K X r 0)).zero_mem
    | add a b ha hb =>
      have hsplit : a + b - Finsupp.linearCombination K (fun _ => (1 : K)) (a + b)
            • Finsupp.single t₀ (1 : K)
          = (a - Finsupp.linearCombination K (fun _ => (1 : K)) a • Finsupp.single t₀ (1 : K))
            + (b - Finsupp.linearCombination K (fun _ => (1 : K)) b • Finsupp.single t₀ (1 : K)) := by
        rw [map_add, add_smul]
        abel
      rw [hsplit]
      exact (LinearMap.range (tupD K X r 0)).add_mem ha hb
    | single t c =>
      have hc : Finsupp.single t c - Finsupp.linearCombination K (fun _ => (1 : K))
            (Finsupp.single t c) • Finsupp.single t₀ (1 : K)
          = c • (Finsupp.single t (1 : K) - Finsupp.single t₀ (1 : K)) := by
        simp only [Finsupp.linearCombination_single, smul_eq_mul, mul_one, smul_sub,
          Finsupp.smul_single_one]
      rw [hc]
      exact (LinearMap.range (tupD K X r 0)).smul_mem c (single_sub_single_mem_range K X t t₀)
  have h := hall y
  rw [hy, zero_smul, sub_zero] at h
  exact h

end Tuple

end OddPAcyclic

/-- **Degree `0` on the models**: over a field, an augmentation cycle of the flat `r`-fold tensor
power of the singular chains of a standard simplex is a boundary. -/
theorem tupD_exists_preimage_zero_of_sum_stdSimplexTop (K : Type) [Field K] (n r : ℕ)
    (y : tupMod K (stdSimplexTop n) r 0)
    (hy : Finsupp.linearCombination K (fun _ => (1 : K)) y = 0) :
    ∃ z : tupMod K (stdSimplexTop n) r 1, tupD K (stdSimplexTop n) r 0 z = y :=
  OddPAcyclic.tupD_exists_preimage_zero_of_pathConnected K (stdSimplexTop n) r y hy

/-- Over every field, a degree-`0` cycle of the augmentation of the flat `r`-fold tensor power of
the signed singular chains of a standard simplex is a boundary. -/
def PrintedTupleAcyclicZeroOnModels : Prop :=
  ∀ (K : Type) [Field K] (n r : ℕ) (y : tupMod K (stdSimplexTop n) r 0),
    Finsupp.linearCombination K (fun _ => (1 : K)) y = 0 →
      ∃ z : tupMod K (stdSimplexTop n) r 1, tupD K (stdSimplexTop n) r 0 z = y

theorem printedTupleAcyclicZeroOnModels : PrintedTupleAcyclicZeroOnModels := by
  intro K _ n r y hy
  exact tupD_exists_preimage_zero_of_sum_stdSimplexTop K n r y hy

#audit_closed_axioms printedTupleAcyclicZeroOnModels

end

end GroupApproximation.CharClass
