import GroupApproximation.CharClass.LIXKGenRotate
import GroupApproximation.CharClass.LIXKGenOfBundle
import GroupApproximation.CharClass.LIXKLocalRestrict
import GroupApproximation.CharClass.LIXKCount
import GroupApproximation.CharClass.RelativeLocalModelOf
import GroupApproximation.CharClass.RelHomotopyInvariance
import GroupApproximation.Meta.AxiomGuard

/-!
# The local classes of the `k`-zero Step C agree, over any field, for every class

Lane `lx-stepcK-agree` (the `LocalClassesAgree` field of `KGen.KZeroStepCDataOf`).

Let `x = s^* u ∈ H^q(N, N ∖ Z; K)` be the pullback of ANY relative class `u` of the bundle pair along
the `k`-section, and `x = ∑_i ρ_i x_i` ANY split into classes of the single-puncture pairs.  Then the
absolute images `j_i(x_i) ∈ H^q(N; K)` are all equal.  Over `F₂` this was free (a nonzero element of an
`F₂`-line is unique); over a field it is the one statement with content, and here it is proved without a
local degree, an orientation, a linear frame or the connectedness of `GL_r(ℂ)`.

## The argument

Let `R := R_{kUnity^i}` be the rotation of `CharClass/LIXKGenRotate.lean`, so `R z_0 = z_i`, and let
`B_i` be the southern half of `N` minus the zeros other than `z_i`.

* **Restriction identifies the local piece.**  `restrictTo B_i` kills `ρ_j x_j` for `j ≠ i` (the pair is
  `(B_i, B_i)` there) and is the excision restriction `F_i` on `ρ_i x_i`, so
  `restrictTo_{B_i} x = F_i x_i`, and `F_i` is injective (`excisionIsoPointOf`).
* **Half B, `R^* x_i = x_0`.**  After `F_0`, the left side is the pullback of `u` along
  `B_0 → B_i → N → E` through `R`, the right side along `B_0 → N → E`.  They agree through the homotopy of
  maps of pairs `(B_0, B_0 ∖ Z) → (E, E ∖ 0)`
  `H(τ, p) = (R_{c(τ)} p, P(R_{c(τ)} p) *ᵥ (0 ⊕ β p))`: the base point moves, the southern field `β` is
  frozen at `p`.  It lies in the bundle because `P` is a projection, it is nonzero off `Z` because the
  southern form is injective on `V`'s fibre, it is the section at `τ = 0`, and at `τ = 1` it is the
  section at `R p` because `β ∘ R = β`.  No zero ever moves, and `G` enters only through `P`.
* **Half A, `j_i x_i = j_0 (R^* x_i)`.**  Naturality of `relToAbs` along `R`, and `R^* = id` on absolute
  cohomology because `R` is homotopic to the identity.

## Main declarations

* `KGen.agreeBall`, `KGen.agreeRes`, `KGen.injective_agreeRes`.
* `KGen.restrictTo_eq_agreeRes` — restriction identifies the local piece.
* `KGen.agreeHomotopy`, `KGen.agreeRes_rotRel` — Half B.
* `KGen.lixKJlocOf_rotRel` — Half A.
* **`KGen.localClassesAgree_of_localSplitOf`** — the field, for every `u` and every split.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-! ## 0. Two generic facts about relative pullbacks -/

/-- Composing two relative pullbacks on an element is the pullback along the composite. -/
theorem relPullback_comp_apply' (R : Type) [CommRing R] {X Y W : TopCat.{0}} (f : X ⟶ Y)
    (g : Y ⟶ W) {A : Set X} {B : Set Y} {C : Set W}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) (hg : ∀ y ∈ B, (ConcreteCategory.hom g) y ∈ C)
    (n : ℕ) (v : relCohomology R W C n) :
    (relPullback R f hf n).hom ((relPullback R g hg n).hom v)
      = (relPullback R (f ≫ g) (fun x hx => hg _ (hf x hx)) n).hom v := by
  rw [relPullback_comp R f g hf hg (fun x hx => hg _ (hf x hx)) n]
  rfl

/-- The relative pullback along equal morphisms, on an element. -/
theorem relPullback_congr_apply' (R : Type) [CommRing R] {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (hfg : f = g) {A : Set X} {B : Set Y} (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ x ∈ A, (ConcreteCategory.hom g) x ∈ B) (n : ℕ) (v : relCohomology R Y B n) :
    (relPullback R f hf n).hom v = (relPullback R g hg n).hom v := by
  subst hfg
  rfl

/-- The relative pullback along the identity between two equal subsets is injective. -/
theorem injective_relPullback_id_of_eq (R : Type) [CommRing R] {W : TopCat.{0}} {A B : Set W}
    (hAB : A = B) (h : ∀ x ∈ A, (ConcreteCategory.hom (𝟙 W)) x ∈ B) (n : ℕ) :
    Function.Injective (relPullback R (𝟙 W) h n).hom := by
  subst hAB
  rw [relPullback_id]
  intro a b hab
  simpa using hab

/-! ## 1. The balls -/

/-- **The southern neighbourhood of the `i`-th zero that contains no other zero.** -/
def agreeBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) : Set (↥sphereOne × Gen.baseM n dd) :=
  {p | circHeight p.1 < 0} ∩ (lixKZero n k dd '' {j | j ≠ i})ᶜ

theorem isOpen_agreeBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    IsOpen (agreeBall n k dd i) :=
  (isOpen_lt (isCircleChart_sphereOne.continuous_height.comp continuous_fst)
    continuous_const).inter
    ((Set.toFinite {j : Fin (k + 1) | j ≠ i}).image (lixKZero n k dd)).isClosed.isOpen_compl

theorem lixKZero_mem_agreeBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    lixKZero n k dd i ∈ agreeBall n k dd i := by
  refine ⟨circHeight_lixKZero_neg n k dd i, ?_⟩
  rintro ⟨j, hj, hji⟩
  exact hj (lixKZero_injective n k dd hji)

theorem lixKZero_notMem_agreeBall (n k : ℕ) (dd : Fin ℓ → ℕ) {i j : Fin (k + 1)} (hji : j ≠ i) :
    lixKZero n k dd j ∉ agreeBall n k dd i :=
  fun h => h.2 ⟨j, hji, rfl⟩

/-- The only zero in `agreeBall i` is `z_i`. -/
theorem eq_of_mem_agreeBall_of_mem_lixKZeroSet (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {p : ↥sphereOne × Gen.baseM n dd} (hp : p ∈ agreeBall n k dd i)
    (hz : p ∈ lixKZeroSet n k dd) : p = lixKZero n k dd i := by
  obtain ⟨j, rfl⟩ := (mem_lixKZeroSet_iff n k dd p).mp hz
  rcases eq_or_ne j i with rfl | hji
  · rfl
  · exact absurd hp (lixKZero_notMem_agreeBall n k dd hji)

/-! ## 2. The restriction to a ball -/

/-- Missing the zero set is missing the `i`-th zero, as a map of pairs out of the ball. -/
theorem agreeBall_mapsTo (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    ∀ y ∈ ((Subtype.val : ↥(agreeBall n k dd i) → ↥sphereOne × Gen.baseM n dd) ⁻¹'
        ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd))),
      (ConcreteCategory.hom (sInclusion (X := lixN n dd) (agreeBall n k dd i))) y ∈
        ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) := by
  intro y hy hyi
  exact hy ((mem_lixKZeroSet_iff n k dd _).mpr ⟨i, Set.mem_singleton_iff.mp hyi⟩)

/-- **The restriction `F_i` from the pair punctured at `z_i` to the ball minus the zero set.** -/
def agreeRes (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) (q : ℕ) :
    relCohomology K (lixN n dd) ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q ⟶
      relCohomology K (TopCat.of ↥(agreeBall n k dd i))
        ((Subtype.val : ↥(agreeBall n k dd i) → ↥sphereOne × Gen.baseM n dd) ⁻¹'
          ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd))) q :=
  relPullback K (sInclusion (X := lixN n dd) (agreeBall n k dd i)) (agreeBall_mapsTo n k dd i) q

/-- On the ball, missing the zero set and missing `z_i` are the same condition. -/
theorem agreeBall_preimage_eq (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    ((Subtype.val : ↥(agreeBall n k dd i) → ↥sphereOne × Gen.baseM n dd) ⁻¹'
        ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)))
      = ((Subtype.val : ↥(agreeBall n k dd i) → ↥sphereOne × Gen.baseM n dd) ⁻¹'
        ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd))) := by
  ext y
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · intro hy hyi
    exact hy ((mem_lixKZeroSet_iff n k dd _).mpr ⟨i, hyi⟩)
  · intro hy hz
    exact hy (eq_of_mem_agreeBall_of_mem_lixKZeroSet n k dd i y.2 hz)

/-- `F_i` is the excision restriction followed by the relabelling of two equal subsets. -/
theorem agreeRes_eq_comp (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (q : ℕ)
    (hsub : ∀ y ∈ ((Subtype.val : ↥(agreeBall n k dd i) → ↥sphereOne × Gen.baseM n dd) ⁻¹'
        ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd))),
      (ConcreteCategory.hom (𝟙 (TopCat.of ↥(agreeBall n k dd i)))) y ∈
        ((Subtype.val : ↥(agreeBall n k dd i) → ↥sphereOne × Gen.baseM n dd) ⁻¹'
          ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)))) :
    agreeRes K n k dd i q
      = (excisionIsoPointOf K (lixN n dd) (lixKZero n k dd i) (agreeBall n k dd i)
          (isOpen_agreeBall n k dd i) (lixKZero_mem_agreeBall n k dd i) q).hom
        ≫ relPullback K (𝟙 (TopCat.of ↥(agreeBall n k dd i))) hsub q := by
  have h := relPullback_comp K (𝟙 (TopCat.of ↥(agreeBall n k dd i)))
    (sInclusion (X := lixN n dd) (agreeBall n k dd i)) hsub (fun _ hy => hy)
    (agreeBall_mapsTo n k dd i) q
  rw [relPullback_eq_of_eq K (Category.id_comp _) (agreeBall_mapsTo n k dd i) q] at h
  exact h

/-- **`F_i` is injective**, by excision. -/
theorem injective_agreeRes (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (q : ℕ) : Function.Injective (agreeRes K n k dd i q).hom := by
  have hsub : ∀ y ∈ ((Subtype.val : ↥(agreeBall n k dd i) → ↥sphereOne × Gen.baseM n dd) ⁻¹'
        ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd))),
      (ConcreteCategory.hom (𝟙 (TopCat.of ↥(agreeBall n k dd i)))) y ∈
        ((Subtype.val : ↥(agreeBall n k dd i) → ↥sphereOne × Gen.baseM n dd) ⁻¹'
          ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd))) := by
    intro y hy
    rw [← agreeBall_preimage_eq n k dd i]
    exact hy
  set E := excisionIsoPointOf K (lixN n dd) (lixKZero n k dd i) (agreeBall n k dd i)
    (isOpen_agreeBall n k dd i) (lixKZero_mem_agreeBall n k dd i) q with hEdef
  have hE : Function.Injective E.hom.hom := by
    refine (injective_iff_map_eq_zero E.hom.hom).mpr fun a ha => ?_
    by_contra hne
    exact ne_zero_of_isoOf E hne ha
  have hid := injective_relPullback_id_of_eq K (agreeBall_preimage_eq n k dd i) hsub q
  intro a b hab
  rw [agreeRes_eq_comp K n k dd i q hsub] at hab
  exact hE (hid hab)

/-! ## 3. Restriction identifies the local piece -/

/-- **`restrictTo_{B_i} x = F_i x_i`** for any split `x = ∑ ρ_j x_j`. -/
theorem restrictTo_eq_agreeRes (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ) (q : ℕ)
    {x : relCohomology K (lixN n dd) ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q}
    {xloc : ∀ i : Fin (k + 1), relCohomology K (lixN n dd)
      ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q}
    (hsplit : LocalSplit (fun i => lixKRhoOf K n k dd i q) x xloc) (i : Fin (k + 1)) :
    (LIXKRelMV.restrictTo K (X := lixN n dd) (agreeBall n k dd i)
        ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q).hom x
      = (agreeRes K n k dd i q).hom (xloc i) := by
  have hs : x = ∑ j, (lixKRhoOf K n k dd j q).hom (xloc j) := hsplit
  rw [hs, map_sum, Finset.sum_eq_single i]
  · show (relPullback K (sInclusion (X := lixN n dd) (agreeBall n k dd i))
        (LIXKRelMV.sInclusion_mapsTo_preimage _ _) q).hom
        ((relPullback K (𝟙 (lixN n dd)) (lixK_mapsTo n k dd i) q).hom (xloc i)) = _
    rw [relPullback_comp_apply']
    exact relPullback_congr_apply' K (Category.comp_id _) _ _ q (xloc i)
  · intro j _ hji
    exact LIXKRelMV.restrictTo_relPullback_id_eq_zero (R := K) (X := lixN n dd)
      (agreeBall n k dd i) (lixK_mapsTo n k dd j)
      (fun y hy hyj => lixKZero_notMem_agreeBall n k dd hji (Set.mem_singleton_iff.mp hyj ▸ hy))
      q (xloc j)
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The section's pullback, restricted to a ball, is the pullback along the composite. -/
theorem restrictTo_lixKSRelOf (K : Type) [Field K] (n k : ℕ) {dd : Fin ℓ → ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) (i : Fin (k + 1))
    (q : ℕ) (u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu) q) :
    (LIXKRelMV.restrictTo K (X := lixN n dd) (agreeBall n k dd i)
        ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q).hom
        ((lixKSRelOf K n k hGc hGu hGe q).hom u)
      = (relPullback K (sInclusion (X := lixN n dd) (agreeBall n k dd i) ≫ lixKS n k hGc hGu hGe)
          (fun x hx => lixKSectionTotal_mapsTo n k hGc hGu hGe _ hx) q).hom u :=
  relPullback_comp_apply' K _ _ _ _ q u

/-! ## 4. Half B: the rotation carries the local piece at `z_i` to the one at `z_0` -/

theorem hR_rot (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    ∀ x ∈ ({lixKZero n k dd 0}ᶜ : Set (↥sphereOne × Gen.baseM n dd)),
      (ConcreteCategory.hom (rotMap n dd (norm_kUnity_pow k (i : ℕ)))) x ∈
        ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) := by
  intro x hx hxi
  refine hx (rotPt_injective n dd (norm_kUnity_pow k (i : ℕ)) ?_)
  rw [rotPt_lixKZero n k dd i (norm_kUnity_pow k (i : ℕ)) rfl]
  exact Set.mem_singleton_iff.mp hxi

/-- **`R^*`, from the pair punctured at `z_i` to the pair punctured at `z_0`.** -/
def rotRel (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) (q : ℕ) :
    relCohomology K (lixN n dd) ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q ⟶
      relCohomology K (lixN n dd) ({lixKZero n k dd 0}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q :=
  relPullback K (rotMap n dd (norm_kUnity_pow k (i : ℕ))) (hR_rot n k dd i) q

variable {dd : Fin ℓ → ℕ}

/-- The rotation carries `agreeBall 0` into `agreeBall i`. -/
theorem rotPt_mem_agreeBall (n k : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) (i : Fin (k + 1))
    {p : ↥sphereOne × Gen.baseM n dd} (hp : p ∈ agreeBall n k dd 0) :
    rotPt n dd (norm_kUnity_pow k (i : ℕ)) p ∈ agreeBall n k dd i := by
  refine ⟨hp.1, ?_⟩
  rintro ⟨j, hji, hj⟩
  have hz : rotPt n dd (norm_kUnity_pow k (i : ℕ)) p ∈ lixKZeroSet n k dd := ⟨j, hj⟩
  have hp0 := eq_of_mem_agreeBall_of_mem_lixKZeroSet n k dd 0 hp
    (mem_lixKZeroSet_of_rotPt n k hGe (norm_kUnity_pow k (i : ℕ)) (kUnity_pow_pow_succ k i) hp.1 hz)
  rw [hp0, rotPt_lixKZero n k dd i (norm_kUnity_pow k (i : ℕ)) rfl] at hj
  exact hji (lixKZero_injective n k dd hj)

/-- A southern point off the zero set rotates off the zero set. -/
theorem rotPt_notMem_lixKZeroSet (n k : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) (i : Fin (k + 1))
    {p : ↥sphereOne × Gen.baseM n dd} (hp : circHeight p.1 < 0) (hz : p ∉ lixKZeroSet n k dd) :
    rotPt n dd (norm_kUnity_pow k (i : ℕ)) p ∉ lixKZeroSet n k dd :=
  fun h => hz (mem_lixKZeroSet_of_rotPt n k hGe (norm_kUnity_pow k (i : ℕ))
    (kUnity_pow_pow_succ k i) hp h)

/-- **The rotation, between the balls.** -/
def rotBall (n k : ℕ) {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) (i : Fin (k + 1)) :
    TopCat.of ↥(agreeBall n k dd 0) ⟶ TopCat.of ↥(agreeBall n k dd i) :=
  TopCat.ofHom ⟨fun p => ⟨rotPt n dd (norm_kUnity_pow k (i : ℕ)) p.1,
      rotPt_mem_agreeBall n k hGe i p.2⟩,
    ((continuous_rotPt_param n dd (c := fun _ : ↥(agreeBall n k dd 0) => kUnity k ^ (i : ℕ))
      continuous_const (fun _ => norm_kUnity_pow k (i : ℕ)) continuous_subtype_val)).subtype_mk _⟩

theorem rotBall_mapsTo (n k : ℕ) {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) (i : Fin (k + 1)) :
    ∀ y ∈ ((Subtype.val : ↥(agreeBall n k dd 0) → ↥sphereOne × Gen.baseM n dd) ⁻¹'
        ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd))),
      (ConcreteCategory.hom (rotBall n k hGe i)) y ∈
        ((Subtype.val : ↥(agreeBall n k dd i) → ↥sphereOne × Gen.baseM n dd) ⁻¹'
          ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd))) :=
  fun y hy => rotPt_notMem_lixKZeroSet n k hGe i y.2.1 hy

theorem sInclusion_comp_rotMap (n k : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) (i : Fin (k + 1)) :
    sInclusion (X := lixN n dd) (agreeBall n k dd 0) ≫ rotMap n dd (norm_kUnity_pow k (i : ℕ))
      = rotBall n k hGe i ≫ sInclusion (X := lixN n dd) (agreeBall n k dd i) :=
  TopCat.hom_ext (ContinuousMap.ext fun _ => rfl)

/-- **The frozen-field homotopy** from the section on `agreeBall 0` to the section precomposed with the
rotation. -/
def agreeHomotopy (n k : ℕ) {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) (i : Fin (k + 1)) :
    TopCat.Homotopy (sInclusion (X := lixN n dd) (agreeBall n k dd 0) ≫ lixKS n k hGc hGu hGe)
      (rotBall n k hGe i ≫ (sInclusion (X := lixN n dd) (agreeBall n k dd i)
        ≫ lixKS n k hGc hGu hGe)) where
  toFun q :=
    ⟨(rotPt n dd (norm_rotPath k i (q.1 : ℝ)) q.2.1,
      mappingTorus (Gen.Vmat n) G circHoriz circHeight (rotPt n dd (norm_rotPath k i (q.1 : ℝ)) q.2.1)
        *ᵥ Sum.elim 0 (blockSouth (aVecK n) (bVecK n k) (fun m : Gen.baseM n dd => Gen.cVec m.2)
          lixChi circHoriz q.2.1)), by
      show mappingTorus (Gen.Vmat n) G circHoriz circHeight _ *ᵥ
          (mappingTorus (Gen.Vmat n) G circHoriz circHeight _ *ᵥ _) = _
      rw [Matrix.mulVec_mulVec,
        (isStarProjection_mappingTorus_lix n hGu _).isIdempotentElem.eq]⟩
  continuous_toFun := by
    have hrot : Continuous fun q : unitInterval × ↥(agreeBall n k dd 0) =>
        rotPt n dd (norm_rotPath k i (q.1 : ℝ)) q.2.1 :=
      continuous_rotPt_param n dd ((continuous_rotPath k i).comp
        (continuous_subtype_val.comp continuous_fst)) (fun q => norm_rotPath k i (q.1 : ℝ))
        (continuous_subtype_val.comp continuous_snd)
    have hP := (continuous_mappingTorus_lix n hGc).comp hrot
    have hβ : Continuous fun q : unitInterval × ↥(agreeBall n k dd 0) =>
        Sum.elim (0 : Gen.VIdx n dd → ℂ) (blockSouth (aVecK n) (bVecK n k)
          (fun m : Gen.baseM n dd => Gen.cVec m.2) lixChi circHoriz q.2.1) :=
      continuous_sumElim_right
        ((lixKSectionData n hGe).continuous_south.comp (continuous_subtype_val.comp continuous_snd))
    exact (hrot.prodMk (hP.matrix_mulVec hβ)).subtype_mk _
  map_zero_left p := by
    have hr : rotPt n dd (norm_rotPath k i ((0 : unitInterval) : ℝ)) p.1 = p.1 :=
      rotPt_of_eq_one n dd _ (by rw [Set.Icc.coe_zero, rotPath_zero]) p.1
    apply Subtype.ext
    show ((rotPt n dd (norm_rotPath k i ((0 : unitInterval) : ℝ)) p.1,
        mappingTorus (Gen.Vmat n) G circHoriz circHeight
            (rotPt n dd (norm_rotPath k i ((0 : unitInterval) : ℝ)) p.1)
          *ᵥ Sum.elim 0 (blockSouth (aVecK n) (bVecK n k) (fun m : Gen.baseM n dd => Gen.cVec m.2)
            lixChi circHoriz p.1)) : ↥sphereOne × Gen.baseM n dd × (_ → ℂ))
      = (p.1, lixKSection n k G p.1)
    rw [hr, lixKSection_of_circHeight_neg n k G p.2.1]
  map_one_left p := by
    have hr : rotPt n dd (norm_rotPath k i ((1 : unitInterval) : ℝ)) p.1
        = rotPt n dd (norm_kUnity_pow k (i : ℕ)) p.1 :=
      rotPt_congr n dd (by rw [Set.Icc.coe_one, rotPath_one]) _ _ p.1
    apply Subtype.ext
    show ((rotPt n dd (norm_rotPath k i ((1 : unitInterval) : ℝ)) p.1,
        mappingTorus (Gen.Vmat n) G circHoriz circHeight
            (rotPt n dd (norm_rotPath k i ((1 : unitInterval) : ℝ)) p.1)
          *ᵥ Sum.elim 0 (blockSouth (aVecK n) (bVecK n k) (fun m : Gen.baseM n dd => Gen.cVec m.2)
            lixChi circHoriz p.1)) : ↥sphereOne × Gen.baseM n dd × (_ → ℂ))
      = (rotPt n dd (norm_kUnity_pow k (i : ℕ)) p.1,
          lixKSection n k G (rotPt n dd (norm_kUnity_pow k (i : ℕ)) p.1))
    rw [hr, lixKSection_of_circHeight_neg n k G
      (show circHeight (rotPt n dd (norm_kUnity_pow k (i : ℕ)) p.1).1 < 0 from p.2.1),
      blockSouth_rotPt n k dd (norm_kUnity_pow k (i : ℕ)) (kUnity_pow_pow_succ k i) p.1]

/-- **The frozen-field homotopy is a homotopy of maps of pairs.** -/
theorem agreeHomotopy_mapsTo (n k : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) (i : Fin (k + 1)) :
    ∀ (t : unitInterval) (x : ↥(agreeBall n k dd 0)),
      x ∈ ((Subtype.val : ↥(agreeBall n k dd 0) → ↥sphereOne × Gen.baseM n dd) ⁻¹'
        ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd))) →
      agreeHomotopy n k hGc hGu hGe i (t, x) ∈ lixPuncturedInTotal n hGc hGu := by
  intro t x hx
  refine ⟨(agreeHomotopy n k hGc hGu hGe i (t, x)).2, ?_⟩
  show mappingTorus (Gen.Vmat n) G circHoriz circHeight (rotPt n dd (norm_rotPath k i (t : ℝ)) x.1)
      *ᵥ Sum.elim 0 (blockSouth (aVecK n) (bVecK n k) (fun m : Gen.baseM n dd => Gen.cVec m.2)
        lixChi circHoriz x.1) ≠ 0
  intro h0
  have hw : Gen.Vmat n (rotPt n dd (norm_rotPath k i (t : ℝ)) x.1).2
      *ᵥ blockSouth (aVecK n) (bVecK n k) (fun m : Gen.baseM n dd => Gen.cVec m.2) lixChi
        circHoriz x.1
      = blockSouth (aVecK n) (bVecK n k) (fun m : Gen.baseM n dd => Gen.cVec m.2) lixChi
        circHoriz x.1 := by
    rw [Vmat_rotPt]
    exact (lixKSectionData n hGe).south_mem x.1
  have hβ := (mappingTorus_mulVec_inr_eq_zero_iff n (G := G)
    (p := rotPt n dd (norm_rotPath k i (t : ℝ)) x.1) x.2.1 hw).mp h0
  have hs : lixKSection n k G x.1 = 0 := by
    rw [lixKSection_of_circHeight_neg n k G x.2.1, hβ, Sum.elim_zero_zero, Matrix.mulVec_zero]
  obtain ⟨j, hj⟩ := (lixKSection_eq_zero_iff n hGe x.1).mp hs
  exact hx ((mem_lixKZeroSet_iff n k dd x.1).mpr ⟨j, hj⟩)

/-- **Half B: `R^* x_i = x_0` after `F_0`**, for every relative class `u` and every split. -/
theorem agreeRes_rotRel (K : Type) [Field K] (n k : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) (q : ℕ)
    (u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu) q)
    {xloc : ∀ i : Fin (k + 1), relCohomology K (lixN n dd)
      ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q}
    (hsplit : LocalSplit (fun i => lixKRhoOf K n k dd i q)
      ((lixKSRelOf K n k hGc hGu hGe q).hom u) xloc) (i : Fin (k + 1)) :
    (agreeRes K n k dd 0 q).hom ((rotRel K n k dd i q).hom (xloc i))
      = (agreeRes K n k dd 0 q).hom (xloc 0) := by
  -- the right side is the section's pullback on the ball at `z_0`
  have hright : (agreeRes K n k dd 0 q).hom (xloc 0)
      = (relPullback K (sInclusion (X := lixN n dd) (agreeBall n k dd 0) ≫ lixKS n k hGc hGu hGe)
          (fun x hx => lixKSectionTotal_mapsTo n k hGc hGu hGe _ hx) q).hom u := by
    rw [← restrictTo_eq_agreeRes K n k dd q hsplit 0, restrictTo_lixKSRelOf]
  -- the left side, through the ball at `z_i`
  have hleft : (agreeRes K n k dd 0 q).hom ((rotRel K n k dd i q).hom (xloc i))
      = (relPullback K (rotBall n k hGe i ≫ (sInclusion (X := lixN n dd) (agreeBall n k dd i)
          ≫ lixKS n k hGc hGu hGe))
          (fun x hx => lixKSectionTotal_mapsTo n k hGc hGu hGe _
            (rotBall_mapsTo n k hGe i x hx)) q).hom u := by
    show (relPullback K (sInclusion (X := lixN n dd) (agreeBall n k dd 0))
        (agreeBall_mapsTo n k dd 0) q).hom
        ((relPullback K (rotMap n dd (norm_kUnity_pow k (i : ℕ))) (hR_rot n k dd i) q).hom
          (xloc i)) = _
    rw [relPullback_comp_apply', relPullback_congr_apply' K (sInclusion_comp_rotMap n k hGe i) _
      (fun x hx => agreeBall_mapsTo n k dd i _ (rotBall_mapsTo n k hGe i x hx)) q (xloc i),
      ← relPullback_comp_apply' K (rotBall n k hGe i) (sInclusion (X := lixN n dd) (agreeBall n k dd i))
        (rotBall_mapsTo n k hGe i) (agreeBall_mapsTo n k dd i) q (xloc i)]
    show (relPullback K (rotBall n k hGe i) (rotBall_mapsTo n k hGe i) q).hom
        ((agreeRes K n k dd i q).hom (xloc i)) = _
    rw [← restrictTo_eq_agreeRes K n k dd q hsplit i, restrictTo_lixKSRelOf, relPullback_comp_apply']
  rw [hleft, hright]
  exact (relPullback_eq_of_homotopy K _ _ (agreeHomotopy n k hGc hGu hGe i)
    (agreeHomotopy_mapsTo n k hGc hGu hGe i) q ▸ rfl :
      (relPullback K (sInclusion (X := lixN n dd) (agreeBall n k dd 0) ≫ lixKS n k hGc hGu hGe)
        (fun x hx => lixKSectionTotal_mapsTo n k hGc hGu hGe _ hx) q).hom u
      = (relPullback K (rotBall n k hGe i ≫ (sInclusion (X := lixN n dd) (agreeBall n k dd i)
          ≫ lixKS n k hGc hGu hGe))
          (fun x hx => lixKSectionTotal_mapsTo n k hGc hGu hGe _
            (rotBall_mapsTo n k hGe i x hx)) q).hom u).symm

/-! ## 5. Half A: the rotation does not change the absolute image -/

/-- **`j_0 (R^* v) = j_i v`.** -/
theorem lixKJlocOf_rotRel (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (q : ℕ) (v : relCohomology K (lixN n dd)
      ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q) :
    (lixKJlocOf K n k dd 0 q).hom ((rotRel K n k dd i q).hom v) = (lixKJlocOf K n k dd i q).hom v := by
  have h := relToAbs_naturality K (rotMap n dd (norm_kUnity_pow k (i : ℕ))) (hR_rot n k dd i) q
  have h2 := congrArg (fun φ => φ.hom v) h
  have habs : ∀ a : Hmod K (lixN n dd) q,
      (HomologicalComplex.homologyMap ((singularCochainComplexFunctor K (ModuleCat.of K K)).map
        (rotMap n dd (norm_kUnity_pow k (i : ℕ))).op) q).hom a = a :=
    fun a => pull_rotMap K n k dd i q a
  simp only at h2
  rw [habs] at h2
  exact h2.symm

/-! ## 6. The field -/

/-- **The local classes of the `k`-zero Step C agree, over any field, for every relative class `u` of the
bundle pair and every local split of its section pullback.** -/
theorem localClassesAgree_of_localSplitOf (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) (q : ℕ)
    (u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu) q)
    (xloc : ∀ i : Fin (k + 1), relCohomology K (lixN n dd)
      ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q)
    (hsplit : LocalSplit (fun i => lixKRhoOf K n k dd i q)
      ((lixKSRelOf K n k hGc hGu hGe q).hom u) xloc) :
    LocalClassesAgree (fun i => lixKJlocOf K n k dd i q) xloc
      ((lixKJlocOf K n k dd 0 q).hom (xloc 0)) := by
  intro i
  have hrot : (rotRel K n k dd i q).hom (xloc i) = xloc 0 :=
    injective_agreeRes K n k dd 0 q (agreeRes_rotRel K n k hGc hGu hGe q u hsplit i)
  show (lixKJlocOf K n k dd i q).hom (xloc i) = (lixKJlocOf K n k dd 0 q).hom (xloc 0)
  rw [← lixKJlocOf_rotRel K n k dd i q (xloc i), hrot]

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.injective_agreeRes
#audit_axioms KGen.restrictTo_eq_agreeRes
#audit_axioms KGen.agreeRes_rotRel
#audit_axioms KGen.lixKJlocOf_rotRel
#audit_axioms KGen.localClassesAgree_of_localSplitOf

end GroupApproximation.CharClass
