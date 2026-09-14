import GroupApproximation.Dynamics.ClopenCrossedProduct
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The faithful action of `M_m(LC(X, F₂) ⋊ ℤ)` on sites

`simple_kazhdan_sofic_group.tex` at 696c4b602, section "LEF groups" (l.482–485):

> The ring $M_m(\LC(X,\F_2)\rtimes\Z)$ acts faithfully on
> $\bigoplus_{x\in X,\,t\in\Z}\F_2^m$ by $f\delta_{x,t}=f(T^tx)\delta_{x,t}$ and
> $u\delta_{x,t}=\delta_{x,t+1}$.

For a homeomorphism `T` of a topological space `X` and a commutative ring `k`:

* `rho T k : LC(X, k) ⋊_T ℤ →+* End_k(k^{(X × ℤ)})`: a coefficient `f` acts by
  `δ_{x,t} ↦ f(T^t x) δ_{x,t}` (`rho_coeff_single`), and `u` by `δ_{x,t} ↦ δ_{x,t+1}`
  (`rho_unit_single`). The covariance `u f u⁻¹ = f ∘ T⁻¹` holds because `T⁻¹(T^{t+1} x) = T^t x`.
* `rho_injective`: the action is faithful. A coefficient read at `(T^{-j} y, 0)` and
  level `j` is the value at `y` of the Laurent coefficient at `u^j`.
* `rhoMat T k m`: the action of `M_m(R_X)` on `(k^{(X × ℤ)})^m`, through
  `endVecRingEquivMatrixEnd`, and `rhoMat_injective`.
* The displacement calculus used by the dimension count of the next sentence:
  - `NearSite x0 t D v`: every component of `v` is supported at base point `x0`, within `D`
    levels of `t`;
  - `HasDisplacement D E`: `E` moves such vectors at most `D` levels;
  - `UDegreeLE w x`: `x` involves only `u^j` with `|j| ≤ w`.
  A matrix whose entries involve only `u^j` with `|j| ≤ w` has displacement `w`
  (`hasDisplacement_rhoMat`). Displacements add under products (`HasDisplacement.mul`,
  `HasDisplacement.pow`), and every matrix has some finite displacement (`exists_hasDisplacement`).
* `printedSiteActionFaithful`: the printed sentence over `F₂`, for every `X`, `T` and `m`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SiteAction

open Finsupp
open Multiplicative (ofAdd toAdd)

section Action

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type*) [CommRing k]

theorem zpow_neg_add_apply (j t : ℤ) (x : X) : (T ^ (-j)) ((T ^ (t + j)) x) = (T ^ t) x := by
  rw [← Homeomorph.mul_apply, ← zpow_add, show -j + (t + j) = t by ring]

theorem zpow_apply_zpow_neg_apply (j : ℤ) (y : X) : (T ^ j) ((T ^ (-j)) y) = y := by
  rw [← Homeomorph.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, Homeomorph.one_apply]

/-- **The diagonal action** `δ_{x,t} ↦ f(T^t x) δ_{x,t}` of a coefficient `f ∈ LC(X, k)`. -/
noncomputable def diag (f : LocallyConstant X k) : Module.End k (X × ℤ →₀ k) where
  toFun w := Finsupp.onFinset w.support (fun p => f ((T ^ p.2) p.1) * w p)
    (fun p hp => Finsupp.mem_support_iff.2 fun h0 => hp (by rw [h0, mul_zero]))
  map_add' v w := Finsupp.ext fun p => by
    simp only [Finsupp.onFinset_apply, Finsupp.add_apply, mul_add]
  map_smul' c w := Finsupp.ext fun p => by
    simp only [Finsupp.onFinset_apply, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem diag_apply (f : LocallyConstant X k) (w : X × ℤ →₀ k) (p : X × ℤ) :
    diag T k f w p = f ((T ^ p.2) p.1) * w p :=
  rfl

theorem diag_single (f : LocallyConstant X k) (p : X × ℤ) (c : k) :
    diag T k f (single p c) = single p (f ((T ^ p.2) p.1) * c) :=
  Finsupp.ext fun q => by
    classical
    rw [diag_apply, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with h
    · rw [h]
    · rw [mul_zero]

/-- The diagonal action as a ring homomorphism `LC(X, k) →+* End(k^{(X × ℤ)})`. -/
noncomputable def diagHom : LocallyConstant X k →+* Module.End k (X × ℤ →₀ k) where
  toFun := diag T k
  map_one' := LinearMap.ext fun w => Finsupp.ext fun p => by
    show (1 : k) * w p = w p
    rw [one_mul]
  map_mul' f g := LinearMap.ext fun w => Finsupp.ext fun p => by
    show f ((T ^ p.2) p.1) * g ((T ^ p.2) p.1) * w p =
      f ((T ^ p.2) p.1) * (g ((T ^ p.2) p.1) * w p)
    rw [mul_assoc]
  map_zero' := LinearMap.ext fun w => Finsupp.ext fun p => by
    show (0 : k) * w p = 0
    rw [zero_mul]
  map_add' f g := LinearMap.ext fun w => Finsupp.ext fun p => by
    show (f ((T ^ p.2) p.1) + g ((T ^ p.2) p.1)) * w p =
      f ((T ^ p.2) p.1) * w p + g ((T ^ p.2) p.1) * w p
    rw [add_mul]

/-- The coefficients of `R_X` acting diagonally. -/
noncomputable def coeffHom : ClopenCoeff T k →+* Module.End k (X × ℤ →₀ k) :=
  (diagHom T k).comp (ClopenCoeff.of T k).symm.toRingHom

theorem coeffHom_apply (a : ClopenCoeff T k) :
    coeffHom T k a = diag T k ((ClopenCoeff.of T k).symm a) :=
  rfl

/-- The level shift `δ_{x,t} ↦ δ_{x,t+j}`. -/
noncomputable def shiftLin (j : ℤ) : Module.End k (X × ℤ →₀ k) where
  toFun w := Finsupp.mapDomain (fun p : X × ℤ => (p.1, p.2 + j)) w
  map_add' _ _ := Finsupp.mapDomain_add
  map_smul' c w := Finsupp.mapDomain_smul c w

omit [TopologicalSpace X] in
theorem shiftLin_single (j : ℤ) (p : X × ℤ) (c : k) :
    shiftLin (X := X) k j (single p c) = single (p.1, p.2 + j) c :=
  Finsupp.mapDomain_single

/-- The powers of the level shift. -/
noncomputable def shiftHom : Multiplicative ℤ →* Module.End k (X × ℤ →₀ k) where
  toFun m := shiftLin k (toAdd m)
  map_one' := Finsupp.lhom_ext fun p c => by
    rw [shiftLin_single, toAdd_one, add_zero, Module.End.one_apply]
  map_mul' m n := Finsupp.lhom_ext fun p c => by
    rw [Module.End.mul_apply, shiftLin_single, shiftLin_single, shiftLin_single, toAdd_mul]
    congr 1
    ext
    · rfl
    · show p.2 + (toAdd m + toAdd n) = p.2 + toAdd n + toAdd m
      ring

omit [TopologicalSpace X] in
theorem shiftHom_apply (m : Multiplicative ℤ) :
    shiftHom (X := X) k m = shiftLin k (toAdd m) :=
  rfl

/-- **Covariance** in the representation: `(f ∘ T^{−j}) σ^j = σ^j f`. -/
theorem coeffHom_smul_mul_shiftHom (x : ClopenCoeff T k) (y : Multiplicative ℤ) :
    coeffHom T k (y • x) * shiftHom k y = shiftHom k y * coeffHom T k x := by
  refine Finsupp.lhom_ext fun p c => ?_
  obtain ⟨x0, t⟩ := p
  have hval : (ClopenCoeff.of T k).symm (y • x) ((T ^ (t + toAdd y)) x0) =
      (ClopenCoeff.of T k).symm x ((T ^ t) x0) := by
    show (ClopenCoeff.of T k).symm x ((T ^ (-toAdd y)) ((T ^ (t + toAdd y)) x0)) =
      (ClopenCoeff.of T k).symm x ((T ^ t) x0)
    rw [zpow_neg_add_apply]
  rw [Module.End.mul_apply, Module.End.mul_apply, shiftHom_apply, shiftLin_single,
    coeffHom_apply, coeffHom_apply, diag_single, diag_single, shiftLin_single]
  dsimp only
  rw [hval]

/-- **The faithful action** of `R_X = LC(X, k) ⋊_T ℤ` on `k^{(X × ℤ)}` (tex l.482–485). -/
noncomputable def rho : ClopenCrossedProduct T k →+* Module.End k (X × ℤ →₀ k) :=
  SkewMonoidAlgebra.liftNCRingHom (coeffHom T k) (shiftHom k) fun {x y} =>
    coeffHom_smul_mul_shiftHom T k x y

theorem rho_single (g : Multiplicative ℤ) (a : ClopenCoeff T k) :
    rho T k (SkewMonoidAlgebra.single g a) = coeffHom T k a * shiftHom k g := by
  show SkewMonoidAlgebra.liftNC (coeffHom T k : ClopenCoeff T k →+ Module.End k (X × ℤ →₀ k))
    (shiftHom k) (SkewMonoidAlgebra.single g a) = coeffHom T k a * shiftHom k g
  exact SkewMonoidAlgebra.liftNC_single _ _ _ _

open Classical in
/-- **Matrix entries of the action**: `(ρ(x) (c δ_{x0,i}))(y, l) = [x0 = y] x_{l−i}(T^l x0) c`. -/
theorem rho_apply_single_apply (x : ClopenCrossedProduct T k) (x0 : X) (i : ℤ) (c : k) (y : X)
    (l : ℤ) :
    rho T k x (single (x0, i) c) (y, l) =
      if x0 = y then
        (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x (ofAdd (l - i))) ((T ^ l) x0) * c
      else 0 := by
  induction x using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | single g a =>
      rw [rho_single, Module.End.mul_apply, shiftHom_apply, shiftLin_single, coeffHom_apply,
        diag_single, Finsupp.single_apply, SkewMonoidAlgebra.coeff_single_apply]
      dsimp only
      by_cases hy : x0 = y
      · by_cases h : g = ofAdd (l - i)
        · have h' : i + toAdd g = l := by
            rw [h, toAdd_ofAdd]
            omega
          rw [if_pos (by rw [hy, h']), if_pos hy, if_pos h, h']
        · have h' : ¬ (x0, i + toAdd g) = (y, l) := fun h'' => h (by
            have hs := congrArg Prod.snd h''
            dsimp only at hs
            have ht : toAdd g = l - i := by omega
            rw [← ht, ofAdd_toAdd])
          rw [if_neg h', if_pos hy, if_neg h]
          simp
      · have h' : ¬ (x0, i + toAdd g) = (y, l) := fun h'' => hy (congrArg Prod.fst h'')
        rw [if_neg h', if_neg hy]
  | add p q hp hq =>
      rw [map_add, LinearMap.add_apply, Finsupp.add_apply, hp, hq, SkewMonoidAlgebra.coeff_add,
        Finsupp.add_apply, map_add]
      split_ifs
      · exact (add_mul _ _ _).symm
      · simp

/-- **The action is faithful** (tex l.482–485). -/
theorem rho_injective : Function.Injective (rho T k) := by
  refine (injective_iff_map_eq_zero (rho T k)).2 fun x hx => ?_
  refine SkewMonoidAlgebra.ext fun m => ?_
  have hcoeff : (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x m) = 0 := by
    refine LocallyConstant.ext fun y => ?_
    have h := rho_apply_single_apply T k x ((T ^ (-toAdd m)) y) 0 1 ((T ^ (-toAdd m)) y)
      (toAdd m)
    rw [hx, if_pos rfl, sub_zero, ofAdd_toAdd, mul_one, zpow_apply_zpow_neg_apply] at h
    exact h.symm
  rw [SkewMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact (ClopenCoeff.of T k).symm.injective (hcoeff.trans (map_zero _).symm)

/-- `ρ(f) δ_{x,t} = f(T^t x) δ_{x,t}`. -/
theorem rho_coeff_single (f : LocallyConstant X k) (x : X) (t : ℤ) (c : k) :
    rho T k (ClopenCrossedProduct.coeff T k f) (single (x, t) c) = single (x, t) (f ((T ^ t) x) * c) := by
  rw [ClopenCrossedProduct.coeff_apply, Pestov91.CrossedProduct.C_apply, rho_single, map_one,
    mul_one, coeffHom_apply, diag_single]
  rfl

/-- `ρ(u) δ_{x,t} = δ_{x,t+1}`. -/
theorem rho_unit_single (x : X) (t : ℤ) (c : k) :
    rho T k (ClopenCrossedProduct.unit T k : ClopenCrossedProduct T k) (single (x, t) c) =
      single (x, t + 1) c := by
  have hu := Pestov91.CrossedProduct.val_unit_zpow (A := ClopenCoeff T k) 1
  rw [zpow_one] at hu
  rw [hu, rho_single, map_one, one_mul, shiftHom_apply, toAdd_ofAdd, shiftLin_single]

variable (m : ℕ)

/-- **The action of `M_m(R_X)`** on `(k^{(X × ℤ)})^m`. -/
noncomputable def rhoMat :
    Matrix (Fin m) (Fin m) (ClopenCrossedProduct T k) →+* Module.End k (Fin m → (X × ℤ →₀ k)) :=
  (endVecRingEquivMatrixEnd (Fin m) k (X × ℤ →₀ k)).symm.toRingHom.comp (rho T k).mapMatrix

theorem rhoMat_apply (A : Matrix (Fin m) (Fin m) (ClopenCrossedProduct T k))
    (v : Fin m → (X × ℤ →₀ k)) (i : Fin m) :
    rhoMat T k m A v i = ∑ j, rho T k (A i j) (v j) :=
  rfl

/-- **`M_m(R_X)` acts faithfully** (tex l.482–485). -/
theorem rhoMat_injective : Function.Injective (rhoMat T k m) := by
  intro A B h
  have h' : (rho T k).mapMatrix A = (rho T k).mapMatrix B :=
    (endVecRingEquivMatrixEnd (Fin m) k (X × ℤ →₀ k)).symm.injective h
  exact Matrix.ext fun i j => rho_injective T k (congrFun (congrFun h' i) j)

end Action

section Displacement

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {k : Type*} [CommRing k] {m : ℕ}

/-- Every component of `v` is supported at the base point `x0`, within `D` levels of `t`. -/
def NearSite (x0 : X) (t : ℤ) (D : ℕ) (v : Fin m → (X × ℤ →₀ k)) : Prop :=
  ∀ i, ∀ p ∈ (v i).support, p.1 = x0 ∧ |p.2 - t| ≤ (D : ℤ)

/-- `E` moves vectors near a site by at most `D` levels. -/
def HasDisplacement (D : ℕ) (E : Module.End k (Fin m → (X × ℤ →₀ k))) : Prop :=
  ∀ (x0 : X) (t : ℤ) (D' : ℕ) (v : Fin m → (X × ℤ →₀ k)),
    NearSite x0 t D' v → NearSite x0 t (D' + D) (E v)

/-- `x` involves only `u^j` with `|j| ≤ w`. -/
def UDegreeLE (w : ℕ) (x : ClopenCrossedProduct T k) : Prop :=
  ∀ g ∈ x.support, |toAdd g| ≤ (w : ℤ)

omit [TopologicalSpace X] in
theorem HasDisplacement.mono {D D'' : ℕ} {E : Module.End k (Fin m → (X × ℤ →₀ k))}
    (h : HasDisplacement D E) (hD : D ≤ D'') : HasDisplacement D'' E :=
  fun x0 t D' v hv i p hp => by
    obtain ⟨h1, h2⟩ := h x0 t D' v hv i p hp
    exact ⟨h1, h2.trans (by omega)⟩

omit [TopologicalSpace X] in
theorem hasDisplacement_one : HasDisplacement (X := X) (k := k) (m := m) 0 1 :=
  fun _ _ D' v hv => by
    simpa only [add_zero, Module.End.one_apply] using hv

omit [TopologicalSpace X] in
theorem HasDisplacement.mul {D₁ D₂ : ℕ} {E₁ E₂ : Module.End k (Fin m → (X × ℤ →₀ k))}
    (h₁ : HasDisplacement D₁ E₁) (h₂ : HasDisplacement D₂ E₂) :
    HasDisplacement (D₁ + D₂) (E₁ * E₂) := fun x0 t D' v hv => by
  have h := h₁ x0 t (D' + D₂) (E₂ v) (h₂ x0 t D' v hv)
  rw [Module.End.mul_apply]
  have e : D' + (D₁ + D₂) = D' + D₂ + D₁ := by omega
  rw [e]
  exact h

omit [TopologicalSpace X] in
theorem HasDisplacement.pow {D : ℕ} {E : Module.End k (Fin m → (X × ℤ →₀ k))}
    (h : HasDisplacement D E) : ∀ n : ℕ, HasDisplacement (n * D) (E ^ n)
  | 0 => by
      rw [zero_mul, pow_zero]
      exact hasDisplacement_one
  | n + 1 => by
      rw [pow_succ, add_mul, one_mul]
      exact (HasDisplacement.pow h n).mul h

open Classical in
theorem mem_support_rho_single {x : ClopenCrossedProduct T k} {x0 : X} {i : ℤ} {c : k}
    {q : X × ℤ} (hq : q ∈ (rho T k x (single (x0, i) c)).support) :
    q.1 = x0 ∧ ofAdd (q.2 - i) ∈ x.support := by
  obtain ⟨y, l⟩ := q
  rw [Finsupp.mem_support_iff, rho_apply_single_apply] at hq
  by_cases hy : x0 = y
  · rw [if_pos hy] at hq
    refine ⟨hy.symm, SkewMonoidAlgebra.mem_support_iff.2 fun h0 => hq ?_⟩
    rw [h0, map_zero]
    simp
  · rw [if_neg hy] at hq
    exact absurd rfl hq

theorem nearSite_rho {w : ℕ} {x : ClopenCrossedProduct T k} (hx : UDegreeLE w x) {x0 : X}
    {t : ℤ} {D : ℕ} (u : X × ℤ →₀ k)
    (hu : ∀ p ∈ u.support, p.1 = x0 ∧ |p.2 - t| ≤ (D : ℤ)) :
    ∀ q ∈ (rho T k x u).support, q.1 = x0 ∧ |q.2 - t| ≤ ((D + w : ℕ) : ℤ) := by
  classical
  revert hu
  refine Finsupp.induction u ?_ ?_
  · intro _ q hq
    simp at hq
  · intro a b f ha hb ih hu q hq
    have hfa : f a = 0 := by
      by_contra h
      exact ha (Finsupp.mem_support_iff.2 h)
    have haS : a ∈ (single a b + f).support := by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same, hfa, add_zero]
      exact hb
    have hfS : ∀ p ∈ f.support, p ∈ (single a b + f).support := by
      intro p hp
      have hpa : a ≠ p := fun h => ha (h ▸ hp)
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, if_neg hpa, zero_add]
      exact Finsupp.mem_support_iff.1 hp
    rw [map_add] at hq
    rcases Finset.mem_union.1 (Finsupp.support_add hq) with hq1 | hq1
    · obtain ⟨xa, ia⟩ := a
      obtain ⟨ha1, ha2⟩ := hu (xa, ia) haS
      obtain ⟨hq1a, hq1b⟩ := mem_support_rho_single hq1
      have hdeg := hx _ hq1b
      rw [toAdd_ofAdd] at hdeg
      refine ⟨hq1a.trans ha1, ?_⟩
      rw [abs_le] at ha2 hdeg ⊢
      obtain ⟨h1, h2⟩ := ha2
      obtain ⟨h3, h4⟩ := hdeg
      dsimp only at h1 h2
      constructor <;> push_cast <;> omega
    · exact ih (fun p hp => hu p (hfS p hp)) q hq1

/-- **A matrix involving only `u^j` with `|j| ≤ w` has displacement `w`.** -/
theorem hasDisplacement_rhoMat {w : ℕ} {A : Matrix (Fin m) (Fin m) (ClopenCrossedProduct T k)}
    (hA : ∀ i j, UDegreeLE w (A i j)) : HasDisplacement w (rhoMat T k m A) := by
  classical
  intro x0 t D' v hv i q hq
  rw [rhoMat_apply] at hq
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hq)
  exact nearSite_rho (hA i j) (v j) (hv j) q hj

theorem exists_uDegreeLE (x : ClopenCrossedProduct T k) : ∃ w : ℕ, UDegreeLE w x := by
  classical
  refine ⟨x.support.sup fun g => (toAdd g).natAbs, fun g hg => ?_⟩
  have h := Finset.le_sup (f := fun g : Multiplicative ℤ => (toAdd g).natAbs) hg
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h

/-- **Every matrix has a finite displacement.** -/
theorem exists_hasDisplacement (A : Matrix (Fin m) (Fin m) (ClopenCrossedProduct T k)) :
    ∃ D : ℕ, HasDisplacement D (rhoMat T k m A) := by
  classical
  choose w hw using fun p : Fin m × Fin m => exists_uDegreeLE (A p.1 p.2)
  refine ⟨Finset.univ.sup w, hasDisplacement_rhoMat fun i j g hg => ?_⟩
  exact (hw (i, j) g hg).trans (by exact_mod_cast Finset.le_sup (Finset.mem_univ (i, j)))

end Displacement

/-! ## The printed sentence -/

/-- **tex l.482–485**: `M_m(LC(X, F₂) ⋊ ℤ)` acts faithfully on `⊕_{x,t} F₂^m` by
`f δ_{x,t} = f(T^t x) δ_{x,t}` and `u δ_{x,t} = δ_{x,t+1}`. -/
def PrintedSiteActionFaithful : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (T : X ≃ₜ X) (m : ℕ),
    (∀ (f : LocallyConstant X (ZMod 2)) (x : X) (t : ℤ) (c : ZMod 2),
      rho T (ZMod 2) (ClopenCrossedProduct.coeff T (ZMod 2) f) (single (x, t) c) =
        single (x, t) (f ((T ^ t) x) * c)) ∧
    (∀ (x : X) (t : ℤ) (c : ZMod 2),
      rho T (ZMod 2) (ClopenCrossedProduct.unit T (ZMod 2) : ClopenCrossedProduct T (ZMod 2))
        (single (x, t) c) = single (x, t + 1) c) ∧
    Function.Injective (rhoMat T (ZMod 2) m)

theorem printedSiteActionFaithful : PrintedSiteActionFaithful := fun _ _ T m =>
  ⟨fun f x t c => rho_coeff_single T (ZMod 2) f x t c,
    fun x t c => rho_unit_single T (ZMod 2) x t c, rhoMat_injective T (ZMod 2) m⟩

#audit_closed_axioms printedSiteActionFaithful

end SiteAction
end SimpleKazhdanSofic
end GroupApproximation
