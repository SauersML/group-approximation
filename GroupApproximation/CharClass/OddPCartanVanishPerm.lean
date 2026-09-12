import GroupApproximation.CharClass.OddPShufflePrimRoot
import GroupApproximation.CharClass.OddPTupleFunctor
import GroupApproximation.CharClass.OddPEval
import GroupApproximation.Meta.AxiomGuard

/-!
# The slot permutation `σ_r` over the group ring, for the bad-residue vanishing

The vanishing theorem V (`OddPCartanVanish.lean`) compares two natural chain maps
`W ⊗ C(X) → C(X)^{⊗p}` that are linear over `F_p[ℤ/p]` when the generator acts on the target as
`T ^ r`.  The first is the equivariant diagonal followed by the signed slot permutation
`σ_r = tupPerm (mulPerm p r hr)⁻¹`, which satisfies `σ_r ∘ T = T ^ r ∘ σ_r`
(lx-redpow's `tupT_pow_mul_tupPerm_mulPerm_inv`).  This file packages `σ_r` as a natural
transformation `oddTgt p p 1 ⟶ oddTgt p p r`, and proves the one evaluation fact V uses:

* `tupEval_tupPerm_const` — a constant tuple of cochains concentrated in one EVEN degree does not
  see a slot permutation, since on its support every Koszul exponent is a sum of products of even
  numbers.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

namespace OddPCartanVanish

/-! ## 1. Two tuple-level facts -/

section Tuple

variable (K : Type) [CommRing K] (X : TopCat.{0}) {r : ℕ}

/-- **The pushforward commutes with every signed slot permutation.** -/
theorem tupMap_tupPerm {Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (π : Equiv.Perm (Fin r))
    (x : tupMod K X r k) :
    tupMap K f r k (tupPerm K X r k π x) = tupPerm K Y r k π (tupMap K f r k x) := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
  | single t c =>
    have h : tupMap K f r k (tupPerm K X r k π (Finsupp.single t (1 : K)))
        = tupPerm K Y r k π (tupMap K f r k (Finsupp.single t (1 : K))) := by
      rw [tupPerm_single, map_smul, tupMap_single, tupMap_single, tupPerm_single]
      rfl
    rw [← Finsupp.smul_single_one, map_smul, map_smul, h, map_smul, map_smul]

/-- **A constant tuple of single-degree cochains in an even degree does not see a slot
permutation.** -/
theorem tupEval_tupPerm_const (π : Equiv.Perm (Fin r)) (φ : ∀ n : ℕ, singularCochainGroup K X n)
    (q : ℕ) (hqe : Even q) (hq : ∀ n, n ≠ q → φ n = 0) (k : ℕ) (x : tupMod K X r k) :
    tupEval K X r k (fun _ => φ) (tupPerm K X r k π x) = tupEval K X r k (fun _ => φ) x := by
  have hL : (tupEval K X r k (fun _ => φ)).comp (tupPerm K X r k π)
      = tupEval K X r k (fun _ => φ) := by
    apply Finsupp.lhom_ext'
    intro t
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [tupPerm_single, map_smul, tupEval_single, tupEval_single, smul_eq_mul, permTupIdx_val]
    have hre : ∏ j, tagEvalG K φ (permTup π t.1 j) = ∏ j, tagEvalG K φ (t.1 j) :=
      Equiv.prod_comp π (fun j => tagEvalG K φ (t.1 j))
    rw [hre]
    by_cases hall : ∀ l, (t.1 l).1 = q
    · have h2 : permExp X π t.1
          = 2 * ∑ i : Fin r, ∑ j : Fin r, if i < j ∧ π j < π i then q / 2 * q else 0 := by
        unfold permExp
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hall]
        split_ifs
        · obtain ⟨c, hc⟩ := hqe
          rw [hc, show (c + c) / 2 = c by omega]
          ring
        · rfl
      have hexp : Even (permExp X π t.1) := ⟨_, h2.trans (two_mul _)⟩
      rw [hexp.neg_one_pow, one_mul]
    · obtain ⟨l, hl⟩ := not_forall.mp hall
      have h0 : ∏ j, tagEvalG K φ (t.1 j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ l) (tagEvalG_of_eq_zero K φ (t.1 l) (hq _ hl))
      rw [h0, mul_zero]
  exact LinearMap.congr_fun hL x

end Tuple

/-! ## 2. `σ_r` over the group ring -/

section Target

variable (p : ℕ) [NeZero p]

/-- The slot permutation `ρ`, linear over the group ring from the action through `T` to the action
through `T ^ m`, given `ρ ∘ T = T ^ m ∘ ρ`. -/
def permTgtLin (X : TopCat.{0}) (k m : ℕ) (ρ : Equiv.Perm (Fin p))
    (hρ : ∀ y, tupPerm (ZMod p) X p k ρ (tupT (ZMod p) X p k y)
      = (tupT (ZMod p) X p k ^ m) (tupPerm (ZMod p) X p k ρ y)) :
    @LinearMap (GroupRingZMod p) (GroupRingZMod p) _ _ (RingHom.id (GroupRingZMod p))
      (tupMod (ZMod p) X p k) (tupMod (ZMod p) X p k) _ _
      (tupModule p X p k 1 (dvd_mul_left p 1)) (tupModule p X p k m (dvd_mul_left p m)) :=
  { toFun := tupPerm (ZMod p) X p k ρ
    map_add' := fun u v => map_add _ u v
    map_smul' := fun c y =>
      galAlgHomP_comm p (tupT (ZMod p) X p k ^ 1) (tupT_pow_pow p X p k 1 (dvd_mul_left p 1))
        (tupT (ZMod p) X p k ^ m) (tupT_pow_pow p X p k m (dvd_mul_left p m))
        (tupPerm (ZMod p) X p k ρ) (fun v => by rw [pow_one]; exact hρ v) c y }

/-- The same, as a morphism of modules over the group ring. -/
def permTgtHom (X : TopCat.{0}) (k m : ℕ) (ρ : Equiv.Perm (Fin p))
    (hρ : ∀ (k : ℕ) (y : tupMod (ZMod p) X p k), tupPerm (ZMod p) X p k ρ (tupT (ZMod p) X p k y)
      = (tupT (ZMod p) X p k ^ m) (tupPerm (ZMod p) X p k ρ y)) :
    tupObj p X p k 1 (dvd_mul_left p 1) ⟶ tupObj p X p k m (dvd_mul_left p m) :=
  @ModuleCat.ofHom (GroupRingZMod p) _ (tupMod (ZMod p) X p k) (tupMod (ZMod p) X p k) _
    (tupModule p X p k 1 (dvd_mul_left p 1)) _ (tupModule p X p k m (dvd_mul_left p m))
    (permTgtLin p X k m ρ (hρ k))

theorem permTgtHom_hom_apply (X : TopCat.{0}) (k m : ℕ) (ρ : Equiv.Perm (Fin p)) (hρ)
    (y : tupMod (ZMod p) X p k) :
    (permTgtHom p X k m ρ hρ).hom y = tupPerm (ZMod p) X p k ρ y :=
  rfl

/-- `ρ` as a map of complexes. -/
def permTgtCx (X : TopCat.{0}) (m : ℕ) (ρ : Equiv.Perm (Fin p))
    (hρ : ∀ (k : ℕ) (y : tupMod (ZMod p) X p k), tupPerm (ZMod p) X p k ρ (tupT (ZMod p) X p k y)
      = (tupT (ZMod p) X p k ^ m) (tupPerm (ZMod p) X p k ρ y)) :
    tupCx p X p 1 (dvd_mul_left p 1) ⟶ tupCx p X p m (dvd_mul_left p m) where
  f k := permTgtHom p X k m ρ hρ
  comm' i j hij := by
    have hij' : j + 1 = i := hij
    subst hij'
    rw [tupCx_d, tupCx_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact (tupPerm_tupD (ZMod p) X j ρ y).symm

/-- **`σ_r` as a natural transformation** `oddTgt p p 1 ⟶ oddTgt p p m`. -/
def permTgt (m : ℕ) (ρ : Equiv.Perm (Fin p))
    (hρ : ∀ (X : TopCat.{0}) (k : ℕ) (y : tupMod (ZMod p) X p k),
      tupPerm (ZMod p) X p k ρ (tupT (ZMod p) X p k y)
        = (tupT (ZMod p) X p k ^ m) (tupPerm (ZMod p) X p k ρ y)) :
    oddTgt p p 1 (dvd_mul_left p 1) ⟶ oddTgt p p m (dvd_mul_left p m) where
  app X := permTgtCx p X m ρ (hρ X)
  naturality X Y f := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    simp only [oddTgt_map, HomologicalComplex.comp_f, tupCxMap_f, ModuleCat.hom_comp,
      LinearMap.comp_apply]
    exact (tupMap_tupPerm (ZMod p) X f k ρ y).symm

theorem permTgt_app_f_apply (m : ℕ) (ρ : Equiv.Perm (Fin p)) (hρ) (X : TopCat.{0}) (k : ℕ)
    (y : tupMod (ZMod p) X p k) :
    (((permTgt p m ρ hρ).app X).f k).hom y = tupPerm (ZMod p) X p k ρ y :=
  rfl

/-- **`σ_r = tupPerm (mulPerm p r hr)⁻¹` intertwines `T` with `T ^ r`**, in every degree and at
every space (lx-redpow's `tupT_pow_mul_tupPerm_mulPerm_inv`). -/
theorem tupPerm_mulPerm_inv_tupT (r : ℕ) (hr : Nat.Coprime r p) (X : TopCat.{0}) (k : ℕ)
    (y : tupMod (ZMod p) X p k) :
    tupPerm (ZMod p) X p k (mulPerm p r hr)⁻¹ (tupT (ZMod p) X p k y)
      = (tupT (ZMod p) X p k ^ r) (tupPerm (ZMod p) X p k (mulPerm p r hr)⁻¹ y) := by
  have h := LinearMap.congr_fun (tupT_pow_mul_tupPerm_mulPerm_inv (ZMod p) X k r hr) y
  simp only [Module.End.mul_apply] at h
  exact h.symm

end Target

end OddPCartanVanish

end

end GroupApproximation.CharClass
