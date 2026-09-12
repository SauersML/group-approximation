import GroupApproximation.CharClass.OddPTupleFunctor
import GroupApproximation.CharClass.OddPAcyclic
import GroupApproximation.CharClass.AcyclicModelsExistence
-- `Field (ZMod p)` for `[Fact p.Prime]`: the acyclicity exports are stated over a field, and nothing
-- else in this closure provides the instance
import Mathlib.Algebra.Field.ZMod

/-!
# The augmentations of the odd-primary comparison, and the acyclicity of the target

The acyclic-models existence theorem (`AcyclicModelsExistence.acyclicModelsMap`) extends a natural
degree-`0` map to a natural chain map once both functors carry augmentations to a common module and
the target is acyclic on the models.  At odd `p` the common module is `F_p` with the group ring
acting through its augmentation `grAug : F_p[ℤ/p] → F_p`, every group element to `1`.

This file supplies, for the target `oddTgt p r s hs` of `OddPTupleFunctor.lean`:

* `grAug`, `trivModule`, `trivObj` — the augmentation of the group ring and the trivial module;
* `galAlgHomP_aug` — an `F_p`-linear functional invariant under an automorphism of order `p` is
  linear over the group ring into the trivial module;
* `tgtAug` — **the augmentation of the target**, `tupAug` on the degree-`0` carrier;
* `oddTgt_acyclicOnModels` — **the acyclicity of the target on the models**, from lix-cupone's
  `tupD_exists_preimage_stdSimplexTop`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-! ## 1. The augmentation of the group ring -/

section GroupRingAug

variable (p : ℕ)

/-- **The augmentation of `F_p[ℤ/p]`**: every group element to `1`. -/
def grAug : GroupRingZMod p →ₐ[ZMod p] ZMod p :=
  MonoidAlgebra.lift (ZMod p) (ZMod p) (Multiplicative (ZMod p)) 1

theorem grAug_single (g : Multiplicative (ZMod p)) (c : ZMod p) :
    grAug p (MonoidAlgebra.single g c) = c := by
  rw [grAug, MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one]

theorem grAug_of (g : Multiplicative (ZMod p)) :
    grAug p (MonoidAlgebra.of (ZMod p) (Multiplicative (ZMod p)) g) = 1 := by
  rw [grAug, MonoidAlgebra.lift_of, MonoidHom.one_apply]

theorem grAug_grGen : grAug p (grGen p) = 1 := grAug_single p _ 1

theorem grAug_grS : grAug p (grS p) = 0 := by
  rw [grS, map_sub, grAug_grGen, map_one, sub_self]

theorem grAug_grNorm : grAug p (grNorm p) = 0 := by
  have h : ∀ j ∈ Finset.range p, grAug p (grGen p ^ j) = 1 := fun j _ => by
    rw [map_pow, grAug_grGen, one_pow]
  rw [grNorm, map_sum, Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, ZMod.natCast_self]

/-- `F_p` as a module over the group ring, through the augmentation.  Never an instance. -/
abbrev trivModule : Module (GroupRingZMod p) (ZMod p) :=
  Module.compHom (ZMod p) (grAug p).toRingHom

theorem trivModule_smul (c : GroupRingZMod p) (x : ZMod p) :
    letI := trivModule p
    c • x = grAug p c * x :=
  rfl

/-- The trivial module, as an object. -/
abbrev trivObj : ModuleCat.{0} (GroupRingZMod p) :=
  letI := trivModule p
  ModuleCat.of (GroupRingZMod p) (ZMod p)

variable [NeZero p]

/-- **An invariant functional is linear over the group ring into the trivial module.** -/
theorem galAlgHomP_aug {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (σ : Module.End (ZMod p) V) (hσ : σ ^ p = 1) (f : V →ₗ[ZMod p] ZMod p)
    (hf : ∀ v, f (σ v) = f v) (c : GroupRingZMod p) (v : V) :
    f ((galAlgHomP σ hσ c) v) = grAug p c * f v := by
  have hpow : ∀ (n : ℕ) (w : V), f ((σ ^ n) w) = f w := by
    intro n
    induction n with
    | zero =>
      intro w
      rw [pow_zero, Module.End.one_apply]
    | succ n ih =>
      intro w
      rw [pow_succ', Module.End.mul_apply, hf, ih]
  induction c using MonoidAlgebra.induction_on with
  | hM g =>
    have hV : galAlgHomP σ hσ (MonoidAlgebra.of (ZMod p) (Multiplicative (ZMod p)) g)
        = galEndP σ hσ g := by
      unfold galAlgHomP
      exact MonoidAlgebra.lift_of _ _
    rw [hV, grAug_of, one_mul]
    exact hpow (Multiplicative.toAdd g).val v
  | hadd c₁ c₂ h₁ h₂ =>
    rw [map_add, LinearMap.add_apply, map_add, h₁, h₂, map_add, add_mul]
  | hsmul a c h =>
    rw [map_smul, LinearMap.smul_apply, map_smul, h, map_smul, smul_eq_mul, smul_eq_mul, mul_assoc]

end GroupRingAug

/-! ## 2. The augmentation of the tensor power -/

section TupAug

variable (K : Type) [CommRing K] (X : TopCat.{0}) {r : ℕ}

theorem tupAug_single (t : TupIdx X r 0) : tupAug K X r (Finsupp.single t (1 : K)) = 1 := by
  rw [tupAug, Finsupp.linearCombination_single, one_smul]

/-- The augmentation on the full model. -/
def tupAugAll (K : Type) [CommRing K] (X : TopCat.{0}) (r : ℕ) : tupAllMod K X r →ₗ[K] K :=
  Finsupp.linearCombination K (fun _ => (1 : K))

theorem tupAugAll_single (t : TupAll X r) : tupAugAll K X r (Finsupp.single t (1 : K)) = 1 := by
  rw [tupAugAll, Finsupp.linearCombination_single, one_smul]

theorem tupAugAll_tupIncl (y : tupMod K X r 0) :
    tupAugAll K X r (tupIncl K X r 0 y) = tupAug K X r y := by
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  | single t c =>
    rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul, tupIncl_single, tupAugAll_single,
      tupAug_single]

/-- The boundary of a tagged simplex of degree at most one has coefficient sum `0`. -/
theorem tagAug_tagBd (τ : TagSimp X) (h : τ.1 ≤ 1) :
    Finsupp.linearCombination K (fun _ : TagSimp X => (1 : K)) (tagBd K X τ) = 0 := by
  obtain ⟨n, σ⟩ := τ
  match n, σ, h with
  | 0, _, _ => rw [tagBd_zero, map_zero]
  | 1, σ, _ =>
    rw [tagBd_succ_eq_sum K X 0 σ, map_sum, Fin.sum_univ_two, map_zsmul, map_zsmul,
      Finsupp.linearCombination_single, Finsupp.linearCombination_single, one_smul, Fin.val_zero,
      Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul, add_neg_cancel]
  | n + 2, _, h => exact absurd (show n + 2 ≤ 1 from h) (by omega)

theorem tupAugAll_slotBd_of_le (j : Fin r) (t : TupAll X r) (h : (t j).1 ≤ 1) :
    tupAugAll K X r (slotBd K X j (Finsupp.single t (1 : K))) = 0 := by
  rw [slotBd_single, slotBdGen, map_smul, Finsupp.apply_linearCombination]
  have hfun : (⇑(tupAugAll K X r) ∘ fun τ : TagSimp X =>
      Finsupp.single (Function.update t j τ) (1 : K)) = fun _ => (1 : K) :=
    funext fun τ => tupAugAll_single K X (Function.update t j τ)
  rw [hfun, tagAug_tagBd K X (t j) h, smul_zero]

/-- **The augmentation kills boundaries.** -/
theorem tupAug_tupD (y : tupMod K X r (0 + 1)) : tupAug K X r (tupD K X r 0 y) = 0 := by
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, hu, hv, add_zero]
  | single t c =>
    rw [← Finsupp.smul_single_one, map_smul, map_smul, ← tupAugAll_tupIncl]
    have h := LinearMap.congr_fun (tupIncl_comp_tupD K X 0) (Finsupp.single t (1 : K))
    simp only [LinearMap.comp_apply] at h
    rw [h, tupIncl_single, tupDAll, LinearMap.sum_apply, map_sum]
    have hz : ∀ j ∈ (Finset.univ : Finset (Fin r)),
        tupAugAll K X r (slotBd K X j (Finsupp.single t.1 (1 : K))) = 0 := by
      intro j _
      have h1 : (t.1 j).1 ≤ ∑ l : Fin r, (t.1 l).1 :=
        Finset.single_le_sum (f := fun l => (t.1 l).1) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
      rw [t.2] at h1
      exact tupAugAll_slotBd_of_le K X j t.1 h1
    rw [Finset.sum_eq_zero hz]
    exact smul_zero c

/-- **The augmentation is natural.** -/
theorem tupAug_tupMap {Y : TopCat.{0}} (f : X ⟶ Y) (y : tupMod K X r 0) :
    tupAug K Y r (tupMap K f r 0 y) = tupAug K X r y := by
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  | single t c =>
    rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul, tupMap_single, tupAug_single,
      tupAug_single]

/-- **The augmentation is invariant under the cyclic action**: on tuples of points the Koszul
exponent vanishes. -/
theorem tupAug_tupT (y : tupMod K X r 0) : tupAug K X r (tupT K X r 0 y) = tupAug K X r y := by
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  | single t c =>
    rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul, tupT_single, map_smul,
      tupAug_single, tupAug_single]
    have h0 : rotExp X t.1 = 0 := by
      have hle := tupDeg_le_tot t.1 0
      rw [t.2] at hle
      rw [rotExp, Nat.le_zero.mp hle, zero_mul]
    rw [h0, pow_zero, one_smul]

theorem tupAug_tupT_pow (s : ℕ) (y : tupMod K X r 0) :
    tupAug K X r ((tupT K X r 0 ^ s) y) = tupAug K X r y := by
  induction s generalizing y with
  | zero => rw [pow_zero, Module.End.one_apply]
  | succ s ih => rw [pow_succ', Module.End.mul_apply, tupAug_tupT, ih]

end TupAug

/-! ## 3. The augmentation of the target, and its acyclicity on the models -/

section Target

variable (p : ℕ) [NeZero p]

/-- The augmentation of the degree-`0` carrier, over the group ring. -/
def tgtAugLin (X : TopCat.{0}) (r s : ℕ) (hs : r ∣ s * p) :
    @LinearMap (GroupRingZMod p) (GroupRingZMod p) _ _ (RingHom.id (GroupRingZMod p))
      (tupMod (ZMod p) X r 0) (ZMod p) _ _ (tupModule p X r 0 s hs) (trivModule p) :=
  letI := tupModule p X r 0 s hs
  letI := trivModule p
  { toFun := tupAug (ZMod p) X r
    map_add' := fun u v => map_add _ u v
    map_smul' := fun c y =>
      galAlgHomP_aug p (tupT (ZMod p) X r 0 ^ s) (tupT_pow_pow p X r 0 s hs) (tupAug (ZMod p) X r)
        (fun v => tupAug_tupT_pow (ZMod p) X s v) c y }

/-- **The augmentation of the target functor.** -/
def tgtAug (r s : ℕ) (hs : r ∣ s * p) :
    Augmentation (GroupRingZMod p) (oddTgt p r s hs) (trivObj p) where
  ε X :=
    letI := tupModule p X r 0 s hs
    letI := trivModule p
    ModuleCat.ofHom (tgtAugLin p X r s hs)
  ε_natural X Y φ := by
    letI := tupModule p X r 0 s hs
    letI := tupModule p Y r 0 s hs
    letI := trivModule p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact tupAug_tupMap (ZMod p) X φ y
  ε_d X := by
    change (tupCx p X r s hs).d 1 0 ≫ _ = 0
    rw [tupCx_d]
    letI := tupModule p X r (0 + 1) s hs
    letI := tupModule p X r 0 s hs
    letI := trivModule p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact tupAug_tupD (ZMod p) X y

theorem tgtAug_ε_hom_apply (r s : ℕ) (hs : r ∣ s * p) (X : TopCat.{0})
    (y : tupMod (ZMod p) X r 0) : ((tgtAug p r s hs).ε X).hom y = tupAug (ZMod p) X r y := by
  rfl

/-- The differential of the target, as the named morphism.  Propositional, not definitional:
`ChainComplex.of` guards its differential by a `dite` on `k + 1 = k + 1`, which does not reduce for
a variable `k`. -/
theorem oddTgt_obj_d (r s : ℕ) (hs : r ∣ s * p) (X : TopCat.{0}) (k : ℕ) :
    ((oddTgt p r s hs).obj X).d (k + 1) k = tupDHom p X r k s hs :=
  tupCx_d p X r s hs k

omit [NeZero p] in
/-- lix-cupone's export, stated at the commutative-ring structure of `ZMod p` the target uses.

The export is stated over `[Field K]`, so at `K = ZMod p` its carriers use `Field.toCommRing`, while
the target uses `ZMod.commRing p`.  Applying the export to `y hy` in one term leaves the `Field`
instance pending while `hy` is unified against the export's hypothesis, and the unifier then unfolds
`tupD` on both sides (a heartbeat timeout).  The `have` elaborates the export with its instance
synthesized, so the remaining check compares the two ring structures only. -/
theorem tupD_exists_preimage_stdSimplexTop_zmod [Fact p.Prime] (n r k : ℕ)
    (y : tupMod (ZMod p) (stdSimplexTop n) r (k + 1))
    (hy : tupD (ZMod p) (stdSimplexTop n) r k y = 0) :
    ∃ z : tupMod (ZMod p) (stdSimplexTop n) r (k + 2),
      tupD (ZMod p) (stdSimplexTop n) r (k + 1) z = y := by
  have h := tupD_exists_preimage_stdSimplexTop (ZMod p) n r k
  exact h y hy

/-- **The target is acyclic on the models.** -/
theorem oddTgt_acyclicOnModels [Fact p.Prime] (r s : ℕ) (hs : r ∣ s * p) :
    AcyclicOnModels stdSimplexTop (GroupRingZMod p) (oddTgt p r s hs) where
  exists_preimage n k y hy := by
    rw [oddTgt_obj_d p r s hs (stdSimplexTop n) k] at hy
    obtain ⟨z, hz⟩ := tupD_exists_preimage_stdSimplexTop_zmod p n r k y hy
    refine ⟨z, ?_⟩
    rw [oddTgt_obj_d p r s hs (stdSimplexTop n) (k + 1)]
    exact hz

end Target

end

end GroupApproximation.CharClass
