import GroupApproximation.CharClass.LIXKGenBundle
import GroupApproximation.CharClass.KroneckerContractible
import GroupApproximation.Meta.AxiomGuard

/-!
# The rotation of the `x₀`-plane, and what the `k`-section does under it, at rank `n`

Lane `lx-stepcK-agree` (the `LocalClassesAgree` field of `KGen.KZeroStepCDataOf`, over any field).

`R_c (t, x, y) := (t, (c · x₀, x₁, …, x_n), y)` for a unit scalar `c` is a homeomorphism of
`N = S¹ × S^{2n+1} × Y`.  With `c = kUnity k ^ i` it carries the zero `z_0` to `z_i`.  Three facts about
it are all the `k`-zero Step C needs over a field:

* **the southern field is invariant.**  `Ψ_k` overwrites the zeroth coordinate by `joinC k`, and
  `joinC k (c z) = c^{k+1} · joinC k z`, so `bVecK n k ∘ R_c = bVecK n k` once `c^{k+1} = 1`; `aVecK` is
  constant, `cVec` sees only `y`, and the circle coordinate is untouched (`blockSouth_rotPt`);
* **the zeros are permuted, not moved off.**  On the southern half the section is the mapping torus
  applied to the southern field, and that application is injective on `V`'s fibre, so a southern point
  is a zero iff its rotation is (`mem_lixKZeroSet_of_rotPt`);
* **the rotation is homotopic to the identity**, through `R_{c(τ)}` with `c(τ) = exp (2πiτ·i/(k+1))`, so
  it acts as the identity on absolute cohomology with any coefficients (`pull_rotMap`).

No orientation, local degree or determinant is computed anywhere.

## Main declarations

* `KGen.rotVec`, `KGen.rotPt`, `KGen.rotMap` — the rotation.
* `KGen.rotPt_lixKZero` — `R_{kUnity^i} z_0 = z_i`.
* `KGen.blockSouth_rotPt` — invariance of the southern field.
* `KGen.lixKSection_of_circHeight_neg`, `KGen.mappingTorus_mulVec_inr_eq_zero_iff` — the southern form.
* `KGen.mem_lixKZeroSet_of_rotPt` — a southern point whose rotation is a zero is a zero.
* `KGen.rotPath`, `KGen.rotHomotopy`, `KGen.pull_rotMap` — the rotation acts trivially on `H^q(N; K)`.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.LIX.Powers
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The rotation -/

/-- Multiply the zeroth coordinate by `c`. -/
def rotVec (n : ℕ) (c : ℂ) (x : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  Function.update x 0 (c * x 0)

@[simp] theorem rotVec_apply_zero (n : ℕ) (c : ℂ) (x : Fin (n + 1) → ℂ) :
    rotVec n c x 0 = c * x 0 :=
  Function.update_self _ _ _

theorem rotVec_apply_of_ne (n : ℕ) (c : ℂ) (x : Fin (n + 1) → ℂ) {i : Fin (n + 1)} (hi : i ≠ 0) :
    rotVec n c x i = x i :=
  Function.update_of_ne hi _ _

theorem rotVec_mem {n : ℕ} {c : ℂ} (hc : ‖c‖ = 1) {x : Fin (n + 1) → ℂ}
    (hx : x ∈ unitVectors (Fin (n + 1))) : rotVec n c x ∈ unitVectors (Fin (n + 1)) := by
  rw [mem_unitVectors_iff] at hx ⊢
  rw [← hx]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_ne i 0 with rfl | hi
  · rw [rotVec_apply_zero, norm_mul, hc, one_mul]
  · rw [rotVec_apply_of_ne n c x hi]

/-- **The rotation of `N` in the `x₀`-plane by the unit scalar `c`.** -/
def rotPt (n : ℕ) (dd : Fin ℓ → ℕ) {c : ℂ} (hc : ‖c‖ = 1) (p : ↥sphereOne × Gen.baseM n dd) :
    ↥sphereOne × Gen.baseM n dd :=
  (p.1, (⟨rotVec n c (p.2.1 : Fin (n + 1) → ℂ), rotVec_mem hc p.2.1.2⟩, p.2.2))

@[simp] theorem rotPt_fst (n : ℕ) (dd : Fin ℓ → ℕ) {c : ℂ} (hc : ‖c‖ = 1)
    (p : ↥sphereOne × Gen.baseM n dd) : (rotPt n dd hc p).1 = p.1 := rfl

@[simp] theorem rotPt_snd_snd (n : ℕ) (dd : Fin ℓ → ℕ) {c : ℂ} (hc : ‖c‖ = 1)
    (p : ↥sphereOne × Gen.baseM n dd) : (rotPt n dd hc p).2.2 = p.2.2 := rfl

/-- The rotation depends on the scalar only through its value. -/
theorem rotPt_congr (n : ℕ) (dd : Fin ℓ → ℕ) {c c' : ℂ} (h : c = c') (hc : ‖c‖ = 1) (hc' : ‖c'‖ = 1)
    (p : ↥sphereOne × Gen.baseM n dd) : rotPt n dd hc p = rotPt n dd hc' p := by
  subst h
  rfl

/-- The rotation by `1` is the identity. -/
theorem rotPt_of_eq_one (n : ℕ) (dd : Fin ℓ → ℕ) {c : ℂ} (hc : ‖c‖ = 1) (h : c = 1)
    (p : ↥sphereOne × Gen.baseM n dd) : rotPt n dd hc p = p := by
  subst h
  refine Prod.ext rfl (Prod.ext (Subtype.ext ?_) rfl)
  show Function.update (p.2.1 : Fin (n + 1) → ℂ) 0 (1 * (p.2.1 : Fin (n + 1) → ℂ) 0)
    = (p.2.1 : Fin (n + 1) → ℂ)
  rw [one_mul, Function.update_eq_self]

/-- **Joint continuity of the rotation in the scalar and the point.** -/
theorem continuous_rotPt_param (n : ℕ) (dd : Fin ℓ → ℕ) {Z : Type*} [TopologicalSpace Z]
    {c : Z → ℂ} (hc : Continuous c) (hc1 : ∀ z, ‖c z‖ = 1)
    {f : Z → ↥sphereOne × Gen.baseM n dd} (hf : Continuous f) :
    Continuous fun z => rotPt n dd (hc1 z) (f z) := by
  have hx : Continuous fun z => ((f z).2.1 : Fin (n + 1) → ℂ) :=
    continuous_subtype_val.comp (continuous_fst.comp (continuous_snd.comp hf))
  have hrot : Continuous fun z => rotVec n (c z) ((f z).2.1 : Fin (n + 1) → ℂ) :=
    hx.update 0 (hc.mul ((continuous_apply 0).comp hx))
  exact (continuous_fst.comp hf).prodMk
    ((hrot.subtype_mk _).prodMk (continuous_snd.comp (continuous_snd.comp hf)))

/-- The rotation, as a morphism of `lixN n dd`. -/
def rotMap (n : ℕ) (dd : Fin ℓ → ℕ) {c : ℂ} (hc : ‖c‖ = 1) : lixN n dd ⟶ lixN n dd :=
  TopCat.ofHom ⟨rotPt n dd hc,
    continuous_rotPt_param n dd (c := fun _ : ↥sphereOne × Gen.baseM n dd => c) continuous_const
      (fun _ => hc) continuous_id⟩

@[simp] theorem rotMap_apply (n : ℕ) (dd : Fin ℓ → ℕ) {c : ℂ} (hc : ‖c‖ = 1)
    (p : ↥sphereOne × Gen.baseM n dd) :
    (ConcreteCategory.hom (rotMap n dd hc)) p = rotPt n dd hc p := rfl

/-- The rotation is injective. -/
theorem rotPt_injective (n : ℕ) (dd : Fin ℓ → ℕ) {c : ℂ} (hc : ‖c‖ = 1) :
    Function.Injective (rotPt n dd hc) := by
  intro p q h
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  have h1 : p.1 = q.1 := by
    have h' := congrArg (fun r : ↥sphereOne × Gen.baseM n dd => r.1) h
    exact h'
  have h3 : p.2.2 = q.2.2 := by
    have h' := congrArg (fun r : ↥sphereOne × Gen.baseM n dd => r.2.2) h
    exact h'
  have h2v : rotVec n c (p.2.1 : Fin (n + 1) → ℂ) = rotVec n c (q.2.1 : Fin (n + 1) → ℂ) := by
    have h' := congrArg (fun r : ↥sphereOne × Gen.baseM n dd => (r.2.1 : Fin (n + 1) → ℂ)) h
    exact h'
  have h2 : p.2.1 = q.2.1 := by
    refine Subtype.ext (funext fun j => ?_)
    have hj := congrFun h2v j
    rcases eq_or_ne j 0 with rfl | hj0
    · rw [rotVec_apply_zero, rotVec_apply_zero] at hj
      exact mul_left_cancel₀ hc0 hj
    · rwa [rotVec_apply_of_ne n c _ hj0, rotVec_apply_of_ne n c _ hj0] at hj
  exact Prod.ext h1 (Prod.ext h2 h3)

/-! ## 2. The zeros -/

theorem norm_kUnity_pow (k i : ℕ) : ‖kUnity k ^ i‖ = 1 := by
  rw [norm_pow, kUnity, Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I / ((k + 1 : ℕ) : ℂ)).re = 0 := by
    have hk : ((k + 1 : ℕ) : ℂ) = (((k + 1 : ℕ) : ℝ) : ℂ) := by push_cast; rfl
    rw [hk, Complex.div_ofReal_re]
    simp
  rw [hre, Real.exp_zero, one_pow]

theorem kUnity_pow_pow_succ (k i : ℕ) : (kUnity k ^ i) ^ (k + 1) = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, kUnity_pow, one_pow]

/-- **`R_{kUnity^i}` carries the zero `z_0` to `z_i`.** -/
theorem rotPt_lixKZero (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) {c : ℂ} (hc : ‖c‖ = 1)
    (hci : c = kUnity k ^ (i : ℕ)) :
    rotPt n dd hc (lixKZero n k dd 0) = lixKZero n k dd i := by
  subst hci
  refine Prod.ext rfl (Prod.ext (Subtype.ext ?_) rfl)
  funext j
  rcases eq_or_ne j 0 with rfl | hj
  · show rotVec n (kUnity k ^ (i : ℕ)) (kZeroVec n k 0) 0 = kZeroVec n k i 0
    rw [rotVec_apply_zero, kZeroVec_apply_zero, kZeroVec_apply_zero, kRoot, kRoot, Fin.val_zero,
      pow_zero, one_mul]
  · show rotVec n (kUnity k ^ (i : ℕ)) (kZeroVec n k 0) j = kZeroVec n k i j
    rw [rotVec_apply_of_ne n _ _ hj, kZeroVec_apply_of_ne n k 0 hj, kZeroVec_apply_of_ne n k i hj]

/-! ## 3. The southern field is invariant -/

/-- `joinC k (c z) = joinC k z` for a unit `c` with `c^{k+1} = 1`. -/
theorem joinC_mul_of_pow_eq_one {k : ℕ} {c : ℂ} (hc : ‖c‖ = 1) (hck : c ^ (k + 1) = 1) (z : ℂ) :
    joinC k (c * z) = joinC k z := by
  rw [joinC, joinC, norm_mul, hc, one_mul, mul_pow, hck, one_mul]

/-- **`Ψ_k ∘ R_c = Ψ_k`** for a unit `c` with `c^{k+1} = 1`. -/
theorem psiVec_rotVec {n k : ℕ} {c : ℂ} (hc : ‖c‖ = 1) (hck : c ^ (k + 1) = 1)
    (x : Fin (n + 1) → ℂ) : psiVec n k (rotVec n c x) = psiVec n k x := by
  funext j
  rcases eq_or_ne j 0 with rfl | hj
  · rw [psiVec_apply_zero, psiVec_apply_zero, rotVec_apply_zero, joinC_mul_of_pow_eq_one hc hck]
  · rw [psiVec_apply_of_ne n k _ hj, psiVec_apply_of_ne n k _ hj, rotVec_apply_of_ne n c x hj]

theorem bVecK_rotPt (n k : ℕ) (dd : Fin ℓ → ℕ) {c : ℂ} (hc : ‖c‖ = 1) (hck : c ^ (k + 1) = 1)
    (p : ↥sphereOne × Gen.baseM n dd) :
    bVecK n k (rotPt n dd hc p).2 = bVecK n k p.2 :=
  psiVec_rotVec hc hck _

/-- **The southern field of the `k`-section is invariant under `R_c`.** -/
theorem blockSouth_rotPt (n k : ℕ) (dd : Fin ℓ → ℕ) {c : ℂ} (hc : ‖c‖ = 1)
    (hck : c ^ (k + 1) = 1) (p : ↥sphereOne × Gen.baseM n dd) :
    blockSouth (aVecK n) (bVecK n k) (fun m : Gen.baseM n dd => Gen.cVec m.2) lixChi circHoriz
        (rotPt n dd hc p)
      = blockSouth (aVecK n) (bVecK n k) (fun m : Gen.baseM n dd => Gen.cVec m.2) lixChi circHoriz
        p := by
  have hb := bVecK_rotPt n k dd hc hck p
  funext j
  simp only [blockSouth, manuscriptPath_apply]
  rw [hb]
  rfl

/-- `V` at the rotated point is `V` at the point: `Vmat` sees only `y`. -/
theorem Vmat_rotPt (n : ℕ) (dd : Fin ℓ → ℕ) {c : ℂ} (hc : ‖c‖ = 1)
    (p : ↥sphereOne × Gen.baseM n dd) :
    Gen.Vmat n (rotPt n dd hc p).2 = Gen.Vmat n p.2 := rfl

/-! ## 4. The southern form of the section -/

/-- **On the southern half, the section is the mapping torus applied to the southern field.** -/
theorem lixKSection_of_circHeight_neg (n k : ℕ)
    (G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ)
    {p : ↥sphereOne × Gen.baseM n dd} (hp : circHeight p.1 < 0) :
    lixKSection n k G p
      = mappingTorus (Gen.Vmat n) G circHoriz circHeight p
          *ᵥ Sum.elim 0 (blockSouth (aVecK n) (bVecK n k) (fun m : Gen.baseM n dd => Gen.cVec m.2)
            lixChi circHoriz p) := by
  rw [lixKSection, mtSection, if_neg (not_le.mpr hp)]

/-- **On the southern half, the mapping torus is injective on vectors of `V`'s fibre placed in the
second block.** -/
theorem mappingTorus_mulVec_inr_eq_zero_iff (n : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    {p : ↥sphereOne × Gen.baseM n dd} (hp : circHeight p.1 < 0)
    {w : Gen.VIdx n dd → ℂ} (hw : Gen.Vmat n p.2 *ᵥ w = w) :
    mappingTorus (Gen.Vmat n) G circHoriz circHeight p *ᵥ Sum.elim 0 w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have hs := mtSection_south_form' (V := Gen.Vmat n) (G := G) (y := circHoriz) (t := circHeight)
      (η := fun _ => w) (p := p) hw
    rw [hs] at h
    have hpos : 0 < (1 - circHeight p.1) / 2 := by linarith
    have hc : ((((1 - circHeight p.1) / 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    funext x
    have hx := congrFun h (Sum.inr x)
    simp only [Sum.elim_inr, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hx
    exact (mul_eq_zero.mp hx).resolve_left hc
  · rintro rfl
    rw [Sum.elim_zero_zero, Matrix.mulVec_zero]

/-- All zeros lie on the southern half. -/
theorem circHeight_lixKZero_neg (n k : ℕ) (dd : Fin ℓ → ℕ) (j : Fin (k + 1)) :
    circHeight (lixKZero n k dd j).1 < 0 := by
  show circHeight southPole < 0
  rw [circHeight_southPole]
  norm_num

/-- **A southern point whose rotation is a zero is a zero.** -/
theorem mem_lixKZeroSet_of_rotPt (n k : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    {c : ℂ} (hc : ‖c‖ = 1) (hck : c ^ (k + 1) = 1)
    {p : ↥sphereOne × Gen.baseM n dd} (hp : circHeight p.1 < 0)
    (h : rotPt n dd hc p ∈ lixKZeroSet n k dd) : p ∈ lixKZeroSet n k dd := by
  have hz : lixKSection n k G (rotPt n dd hc p) = 0 := by
    obtain ⟨j, hj⟩ := (mem_lixKZeroSet_iff n k dd _).mp h
    exact (lixKSection_eq_zero_iff n hGe _).mpr ⟨j, hj⟩
  rw [lixKSection_of_circHeight_neg n k G (show circHeight (rotPt n dd hc p).1 < 0 from hp),
    blockSouth_rotPt n k dd hc hck p] at hz
  have hw : Gen.Vmat n (rotPt n dd hc p).2
      *ᵥ blockSouth (aVecK n) (bVecK n k) (fun m : Gen.baseM n dd => Gen.cVec m.2) lixChi
        circHoriz p
      = blockSouth (aVecK n) (bVecK n k) (fun m : Gen.baseM n dd => Gen.cVec m.2) lixChi
        circHoriz p := by
    rw [Vmat_rotPt]
    exact (lixKSectionData n hGe).south_mem p
  have h0 := (mappingTorus_mulVec_inr_eq_zero_iff n (G := G) (p := rotPt n dd hc p) hp hw).mp hz
  have hs : lixKSection n k G p = 0 := by
    rw [lixKSection_of_circHeight_neg n k G hp, h0, Sum.elim_zero_zero, Matrix.mulVec_zero]
  obtain ⟨j, hj⟩ := (lixKSection_eq_zero_iff n hGe p).mp hs
  exact (mem_lixKZeroSet_iff n k dd p).mpr ⟨j, hj⟩

/-! ## 5. The rotation is homotopic to the identity -/

/-- The unit path from `1` to `kUnity k ^ i`. -/
def rotPath (k i : ℕ) (τ : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * τ * (i : ℝ) / ((k : ℝ) + 1) : ℝ) : ℂ) * Complex.I)

theorem norm_rotPath (k i : ℕ) (τ : ℝ) : ‖rotPath k i τ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem continuous_rotPath (k i : ℕ) : Continuous (rotPath k i) := by
  unfold rotPath
  refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
  exact Complex.continuous_ofReal.comp
    ((((continuous_const.mul continuous_id).mul continuous_const).div_const _))

theorem rotPath_zero (k i : ℕ) : rotPath k i 0 = 1 := by
  simp [rotPath]

theorem rotPath_one (k i : ℕ) : rotPath k i 1 = kUnity k ^ i := by
  have hk : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  rw [rotPath, kUnity, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- **The homotopy from the identity of `N` to the rotation by `kUnity k ^ i`.** -/
def rotHomotopy (n k : ℕ) (dd : Fin ℓ → ℕ) (i : ℕ) :
    TopCat.Homotopy (𝟙 (lixN n dd)) (rotMap n dd (norm_kUnity_pow k i)) where
  toFun q := rotPt n dd (norm_rotPath k i (q.1 : ℝ)) q.2
  continuous_toFun :=
    continuous_rotPt_param n dd
      (c := fun q : unitInterval × ↥(lixN n dd) => rotPath k i (q.1 : ℝ))
      ((continuous_rotPath k i).comp (continuous_subtype_val.comp continuous_fst))
      (fun q => norm_rotPath k i (q.1 : ℝ)) continuous_snd
  map_zero_left p := by
    show rotPt n dd (norm_rotPath k i ((0 : unitInterval) : ℝ)) p = p
    exact rotPt_of_eq_one n dd _ (by rw [Set.Icc.coe_zero, rotPath_zero]) p
  map_one_left p := by
    show rotPt n dd (norm_rotPath k i ((1 : unitInterval) : ℝ)) p
      = rotPt n dd (norm_kUnity_pow k i) p
    exact rotPt_congr n dd (by rw [Set.Icc.coe_one, rotPath_one]) _ _ p

/-- **The rotation acts as the identity on `H^q(N; K)`, for any coefficient ring.** -/
theorem pull_rotMap (K : Type) [CommRing K] (n k : ℕ) (dd : Fin ℓ → ℕ) (i q : ℕ)
    (a : Hmod K (lixN n dd) q) :
    pull (rotMap n dd (norm_kUnity_pow k i)) q a = a := by
  rw [← pull_eq_of_homotopyOf K (rotHomotopy n k dd i) q a, pull_id]

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.rotPt_lixKZero
#audit_axioms KGen.blockSouth_rotPt
#audit_axioms KGen.mem_lixKZeroSet_of_rotPt
#audit_axioms KGen.pull_rotMap

end GroupApproximation.CharClass
