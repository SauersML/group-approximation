import GroupApproximation.Meta.AxiomGuard
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.NoncommRing

/-!
# The finitary general linear group `GL_fin(ℤ, k)` and the bilateral shift

`non_mf_groups_exist.tex`, the remark after `cor:dynamic-rank-budget` (tex 1774–1779):

> Nevertheless its unit group is
> \[
>  R_X^\times\cong\GL_{\mathrm{fin}}(\mathbb Z,\F_2)\rtimes\mathbb Z,
> \]
> where $\GL_{\mathrm{fin}}$ means finite matrix support of $g-1$, and
> $\mathbb Z$ acts by the bilateral shift.

This module builds the right-hand side over every commutative ring `k`, acting on `k^{(ℤ)}` with
basis `e_j = single j 1`.

* `HasFiniteMatrixSupport k A`: only finitely many matrix entries `(A e_j)_i` are nonzero;
* `SupportedIn k S A`: `A` takes values in `k^{(S)}` and kills `k^{(ℤ ∖ S)}`;
  `hasFiniteMatrixSupport_iff`: finite matrix support means support in a finite set;
* `GLfin k`: the subgroup of `GL(k^{(ℤ)})` of the `g` for which `g − 1` has finite matrix support;
* `shiftGL k`: the bilateral shift `e_j ↦ e_{j+1}`, with `shiftGL_zpow_single` and
  `shiftGL_zpow_apply`;
* `shiftAction k : Multiplicative ℤ →* MulAut (GLfin k)`: conjugation by the powers of the shift;
* `FinitaryShift k`: the semidirect product `GL_fin(ℤ, k) ⋊ ℤ`.
-/

namespace GroupApproximation

namespace FinitaryGL

open Finsupp
open Multiplicative (ofAdd toAdd)

/-- `xy − 1 = (x − 1)(y − 1) + (x − 1) + (y − 1)`, stated over an arbitrary ring so that it
applies to `Module.End` by unification. -/
theorem ring_mul_sub_one {R : Type*} [Ring R] (x y : R) :
    x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by
  noncomm_ring

/-- `xyz − 1 = x(y − 1)z` when `xz = 1`. -/
theorem ring_conj_sub_one {R : Type*} [Ring R] {x z : R} (hxz : x * z = 1) (y : R) :
    x * y * z - 1 = x * (y - 1) * z := by
  rw [mul_sub, sub_mul, mul_one, hxz]

variable (k : Type*) [CommRing k]

/-- **Finite matrix support**: only finitely many entries `(A e_j)_i` of `A` are nonzero. -/
def HasFiniteMatrixSupport (A : Module.End k (ℤ →₀ k)) : Prop :=
  {p : ℤ × ℤ | A (single p.2 1) p.1 ≠ 0}.Finite

/-- `A` is supported in `S`: it takes values in `k^{(S)}` and kills `k^{(ℤ ∖ S)}`. -/
def SupportedIn (S : Finset ℤ) (A : Module.End k (ℤ →₀ k)) : Prop :=
  (∀ v, A v ∈ supported k k (S : Set ℤ)) ∧ ∀ v ∈ supported k k ((S : Set ℤ)ᶜ), A v = 0

variable {k}

theorem hasFiniteMatrixSupport_zero : HasFiniteMatrixSupport k (0 : Module.End k (ℤ →₀ k)) := by
  have h : {p : ℤ × ℤ | (0 : Module.End k (ℤ →₀ k)) (single p.2 1) p.1 ≠ 0} = ∅ := by
    ext p
    simp
  show Set.Finite {p : ℤ × ℤ | (0 : Module.End k (ℤ →₀ k)) (single p.2 1) p.1 ≠ 0}
  rw [h]
  exact Set.finite_empty

theorem SupportedIn.apply_single_eq_zero {S : Finset ℤ} {A : Module.End k (ℤ →₀ k)}
    (h : SupportedIn k S A) {j : ℤ} (hj : j ∉ S) : A (single j 1) = 0 :=
  h.2 _ (single_mem_supported k 1 (fun h' => hj (Finset.mem_coe.1 h')))

theorem SupportedIn.mono {S S' : Finset ℤ} (hSS' : S ⊆ S') {A : Module.End k (ℤ →₀ k)}
    (h : SupportedIn k S A) : SupportedIn k S' A :=
  ⟨fun v => supported_mono (Finset.coe_subset.2 hSS') (h.1 v),
    fun v hv => h.2 v (supported_mono (Set.compl_subset_compl.2 (Finset.coe_subset.2 hSS')) hv)⟩

theorem SupportedIn.add {S : Finset ℤ} {A B : Module.End k (ℤ →₀ k)} (hA : SupportedIn k S A)
    (hB : SupportedIn k S B) : SupportedIn k S (A + B) :=
  ⟨fun v => Submodule.add_mem _ (hA.1 v) (hB.1 v), fun v hv => by
    rw [LinearMap.add_apply, hA.2 v hv, hB.2 v hv, add_zero]⟩

theorem SupportedIn.mul {S : Finset ℤ} {A B : Module.End k (ℤ →₀ k)} (hA : SupportedIn k S A)
    (hB : SupportedIn k S B) : SupportedIn k S (A * B) :=
  ⟨fun v => hA.1 (B v), fun v hv => by
    rw [Module.End.mul_apply, hB.2 v hv, map_zero]⟩

/-- Finite matrix support is support in a finite set of coordinates. -/
theorem hasFiniteMatrixSupport_iff (A : Module.End k (ℤ →₀ k)) :
    HasFiniteMatrixSupport k A ↔ ∃ S : Finset ℤ, SupportedIn k S A := by
  classical
  constructor
  · intro hA
    have hrow : ∀ j, ∀ i ∈ (A (single j 1)).support,
        i ∈ hA.toFinset.image Prod.fst ∪ hA.toFinset.image Prod.snd := by
      intro j i hi
      have hmem : (i, j) ∈ hA.toFinset := hA.mem_toFinset.2 (mem_support_iff.1 hi)
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst hmem)
    have hcol : ∀ j, j ∉ hA.toFinset.image Prod.fst ∪ hA.toFinset.image Prod.snd →
        A (single j 1) = 0 := by
      intro j hj
      ext i
      by_contra hne
      have hmem : (i, j) ∈ hA.toFinset := hA.mem_toFinset.2 hne
      exact hj (Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.snd hmem))
    refine ⟨hA.toFinset.image Prod.fst ∪ hA.toFinset.image Prod.snd, fun v => ?_, fun v hv => ?_⟩
    · have hv : v ∈ Submodule.span k ((fun i => single i (1 : k)) '' Set.univ) := by
        rw [← supported_eq_span_single, supported_univ]
        exact Submodule.mem_top
      induction hv using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨j, -, rfl⟩ := hx
          exact (mem_supported k _).2 fun i hi =>
            Finset.mem_coe.2 (hrow j i (Finset.mem_coe.1 hi))
      | zero =>
          rw [map_zero]
          exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
          rw [map_add]
          exact Submodule.add_mem _ hx hy
      | smul c x _ hx =>
          rw [map_smul]
          exact Submodule.smul_mem _ c hx
    · rw [supported_eq_span_single] at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨j, hj, rfl⟩ := hx
          exact hcol j fun h => hj (Finset.mem_coe.2 h)
      | zero => exact map_zero A
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul c x _ hx => rw [map_smul, hx, smul_zero]
  · rintro ⟨S, hS⟩
    refine (Finset.finite_toSet (S ×ˢ S)).subset fun p hp => ?_
    have hp' : A (single p.2 1) p.1 ≠ 0 := hp
    have hj : p.2 ∈ S := by
      by_contra hj
      rw [hS.apply_single_eq_zero hj] at hp'
      exact hp' rfl
    have hi : p.1 ∈ S :=
      Finset.mem_coe.1 ((mem_supported k _).1 (hS.1 (single p.2 1))
        (Finset.mem_coe.2 (mem_support_iff.2 hp')))
    exact Finset.mem_coe.2 (Finset.mem_product.2 ⟨hi, hj⟩)

/-- If `g − 1` is supported in `S`, so is `g⁻¹ − 1`: `g` preserves `k^{(S)}` and fixes
`k^{(ℤ ∖ S)}`, hence so does `g⁻¹`. -/
theorem supportedIn_inv {g : LinearMap.GeneralLinearGroup k (ℤ →₀ k)} {S : Finset ℤ}
    (hS : SupportedIn k S ((g : Module.End k (ℤ →₀ k)) - 1)) :
    SupportedIn k S
      (((g⁻¹ : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k)) - 1) := by
  classical
  have hginv : ∀ w, (g : Module.End k (ℤ →₀ k))
      (((g⁻¹ : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k)) w) = w :=
    fun w => by
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply]
  have hinvg : ∀ w, ((g⁻¹ : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k))
      ((g : Module.End k (ℤ →₀ k)) w) = w :=
    fun w => by
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
  have hpres : ∀ w ∈ supported k k (S : Set ℤ),
      ((g⁻¹ : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k)) w ∈
        supported k k (S : Set ℤ) := by
    intro w hw
    set u := ((g⁻¹ : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k)) w
      with hu
    have huS : u.filter (· ∈ S) ∈ supported k k (S : Set ℤ) :=
      (mem_supported' k _).2 fun x hx =>
        filter_apply_neg _ _ (fun h => hx (Finset.mem_coe.2 h))
    have huC : u - u.filter (· ∈ S) ∈ supported k k ((S : Set ℤ)ᶜ) :=
      (mem_supported' k _).2 fun x hx => by
        have hxS : x ∈ S := by
          by_contra h
          exact hx fun h' => h (Finset.mem_coe.1 h')
        rw [Finsupp.sub_apply, filter_apply_pos _ _ hxS, sub_self]
    have hgC : (g : Module.End k (ℤ →₀ k)) (u - u.filter (· ∈ S)) = u - u.filter (· ∈ S) := by
      have h := hS.2 _ huC
      rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
    have hgS : (g : Module.End k (ℤ →₀ k)) (u.filter (· ∈ S)) ∈ supported k k (S : Set ℤ) := by
      have h₁ := hS.1 (u.filter (· ∈ S))
      rw [LinearMap.sub_apply, Module.End.one_apply] at h₁
      have h₂ := Submodule.add_mem _ h₁ huS
      rwa [sub_add_cancel] at h₂
    have hsplit : (g : Module.End k (ℤ →₀ k)) u =
        (g : Module.End k (ℤ →₀ k)) (u.filter (· ∈ S)) + (u - u.filter (· ∈ S)) := by
      rw [← hgC, ← map_add, add_sub_cancel]
    have hgu : (g : Module.End k (ℤ →₀ k)) u = w := by
      rw [hu]
      exact hginv w
    have hC : u - u.filter (· ∈ S) ∈ supported k k (S : Set ℤ) := by
      have hdecomp : u - u.filter (· ∈ S) = w - (g : Module.End k (ℤ →₀ k)) (u.filter (· ∈ S)) := by
        rw [← hgu, hsplit, add_sub_cancel_left]
      rw [hdecomp]
      exact Submodule.sub_mem _ hw hgS
    have hzero : u - u.filter (· ∈ S) = 0 := by
      ext x
      by_cases hx : x ∈ S
      · exact (mem_supported' k _).1 huC x (fun h => h (Finset.mem_coe.2 hx))
      · exact (mem_supported' k _).1 hC x (fun h => hx (Finset.mem_coe.1 h))
    rw [sub_eq_zero] at hzero
    rw [hzero]
    exact huS
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · have e : (((g⁻¹ : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k)) - 1) v =
        -(((g⁻¹ : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k))
          (((g : Module.End k (ℤ →₀ k)) - 1) v)) := by
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hinvg, neg_sub]
    rw [e]
    exact Submodule.neg_mem _ (hpres _ (hS.1 v))
  · have h₁ := hS.2 v hv
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h₁
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    calc ((g⁻¹ : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k)) v
        = ((g⁻¹ : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k))
            ((g : Module.End k (ℤ →₀ k)) v) := by rw [h₁]
      _ = v := hinvg v

variable (k) in
/-- **`GL_fin(ℤ, k)`** (tex 1778): the invertible operators `g` on `k^{(ℤ)}` such that `g − 1`
has finite matrix support. -/
def GLfin : Subgroup (LinearMap.GeneralLinearGroup k (ℤ →₀ k)) where
  carrier := {g | HasFiniteMatrixSupport k ((g : Module.End k (ℤ →₀ k)) - 1)}
  one_mem' := by
    have h : ((1 : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k)) - 1 = 0 :=
      LinearMap.ext fun v => by
        show v - v = 0
        exact sub_self v
    exact (congrArg (HasFiniteMatrixSupport k) h).mpr hasFiniteMatrixSupport_zero
  mul_mem' := by
    intro a b ha hb
    obtain ⟨S, hS⟩ := (hasFiniteMatrixSupport_iff _).1 ha
    obtain ⟨S', hS'⟩ := (hasFiniteMatrixSupport_iff _).1 hb
    refine (hasFiniteMatrixSupport_iff _).2 ⟨S ∪ S', ?_⟩
    have e : ((a * b : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k)) - 1 =
        ((a : Module.End k (ℤ →₀ k)) - 1) * ((b : Module.End k (ℤ →₀ k)) - 1) +
          ((a : Module.End k (ℤ →₀ k)) - 1) + ((b : Module.End k (ℤ →₀ k)) - 1) :=
      ring_mul_sub_one (a : Module.End k (ℤ →₀ k)) b
    rw [e]
    have hA : SupportedIn k (S ∪ S') ((a : Module.End k (ℤ →₀ k)) - 1) :=
      hS.mono Finset.subset_union_left
    have hB : SupportedIn k (S ∪ S') ((b : Module.End k (ℤ →₀ k)) - 1) :=
      hS'.mono Finset.subset_union_right
    exact ((hA.mul hB).add hA).add hB
  inv_mem' := by
    intro g hg
    obtain ⟨S, hS⟩ := (hasFiniteMatrixSupport_iff _).1 hg
    exact (hasFiniteMatrixSupport_iff _).2 ⟨S, supportedIn_inv hS⟩

variable (k) in
/-- **The bilateral shift** `σ e_j = e_{j+1}` of `k^{(ℤ)}`. -/
noncomputable def shiftGL : LinearMap.GeneralLinearGroup k (ℤ →₀ k) :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (Finsupp.domLCongr (Equiv.addRight (1 : ℤ)))

theorem shiftGL_single (j : ℤ) (c : k) :
    ((shiftGL k : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k))
      (single j c) = single (j + 1) c :=
  Finsupp.domLCongr_single (Equiv.addRight (1 : ℤ)) j c

theorem shiftGL_inv_single (j : ℤ) (c : k) :
    (((shiftGL k)⁻¹ : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k))
      (single j c) = single (j - 1) c := by
  have h := shiftGL_single (k := k) (j - 1) c
  rw [sub_add_cancel] at h
  rw [← h, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply]

theorem shiftGL_zpow_single (n j : ℤ) (c : k) :
    (((shiftGL k) ^ n : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k))
      (single j c) = single (j + n) c := by
  induction n using Int.induction_on generalizing j with
  | zero => rw [zpow_zero, Units.val_one, Module.End.one_apply, add_zero]
  | succ n ih =>
      rw [zpow_add_one, Units.val_mul, Module.End.mul_apply, shiftGL_single, ih]
      congr 1
      omega
  | pred n ih =>
      rw [zpow_sub_one, Units.val_mul, Module.End.mul_apply, shiftGL_inv_single, ih]
      congr 1
      omega

theorem shiftGL_zpow_apply (n : ℤ) (w : ℤ →₀ k) (i : ℤ) :
    (((shiftGL k ^ n : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k)) w) i =
      w (i - n) := by
  have e : ((shiftGL k ^ n : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k)) =
      (Finsupp.domLCongr (Equiv.addRight n) : (ℤ →₀ k) ≃ₗ[k] (ℤ →₀ k)).toLinearMap := by
    refine Finsupp.lhom_ext fun j c => ?_
    rw [shiftGL_zpow_single]
    exact (Finsupp.domLCongr_single (Equiv.addRight n) j c).symm
  rw [e]
  exact Finsupp.equivMapDomain_apply _ _ _

/-- Conjugating a finitary operator by a power of the shift gives a finitary operator. -/
theorem conj_mem_GLfin (n : ℤ) {g : LinearMap.GeneralLinearGroup k (ℤ →₀ k)} (hg : g ∈ GLfin k) :
    shiftGL k ^ n * g * (shiftGL k ^ n)⁻¹ ∈ GLfin k := by
  have hD : HasFiniteMatrixSupport k ((g : Module.End k (ℤ →₀ k)) - 1) := hg
  have e : ((shiftGL k ^ n * g * (shiftGL k ^ n)⁻¹ : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) :
        Module.End k (ℤ →₀ k)) - 1 =
      ((shiftGL k ^ n : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k)) *
        ((g : Module.End k (ℤ →₀ k)) - 1) *
          ((shiftGL k ^ (-n) : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) :
            Module.End k (ℤ →₀ k)) := by
    rw [zpow_neg, Units.val_mul, Units.val_mul]
    exact ring_conj_sub_one (R := Module.End k (ℤ →₀ k)) (Units.mul_inv (shiftGL k ^ n)) _
  show HasFiniteMatrixSupport k (((shiftGL k ^ n * g * (shiftGL k ^ n)⁻¹ :
    LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k)) - 1)
  rw [e]
  refine (hD.image fun p : ℤ × ℤ => (p.1 + n, p.2 + n)).subset fun p hp => ?_
  have hp' : (((shiftGL k ^ n : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) :
      Module.End k (ℤ →₀ k)) * ((g : Module.End k (ℤ →₀ k)) - 1) *
        ((shiftGL k ^ (-n) : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) :
          Module.End k (ℤ →₀ k))) (single p.2 1) p.1 ≠ 0 := hp
  rw [Module.End.mul_apply, Module.End.mul_apply, shiftGL_zpow_single, shiftGL_zpow_apply] at hp'
  refine (Set.mem_image _ _ _).2
    ⟨(p.1 - n, p.2 - n), ?_, Prod.ext (sub_add_cancel _ _) (sub_add_cancel _ _)⟩
  show ((g : Module.End k (ℤ →₀ k)) - 1) (single (p.2 - n) 1) (p.1 - n) ≠ 0
  exact hp'

variable (k) in
/-- **The bilateral shift action** (tex 1779): `ℤ` acts on `GL_fin(ℤ, k)` by conjugation with the
powers of the shift. -/
noncomputable def shiftAction : Multiplicative ℤ →* MulAut (GLfin k) where
  toFun a :=
    { toFun := fun g => ⟨shiftGL k ^ toAdd a * g * (shiftGL k ^ toAdd a)⁻¹,
        conj_mem_GLfin _ g.2⟩
      invFun := fun g => ⟨shiftGL k ^ (-toAdd a) * g * (shiftGL k ^ (-toAdd a))⁻¹,
        conj_mem_GLfin _ g.2⟩
      left_inv := fun g => Subtype.ext (by
        show shiftGL k ^ (-toAdd a) * (shiftGL k ^ toAdd a * (g : LinearMap.GeneralLinearGroup k
          (ℤ →₀ k)) * (shiftGL k ^ toAdd a)⁻¹) * (shiftGL k ^ (-toAdd a))⁻¹ = g
        group)
      right_inv := fun g => Subtype.ext (by
        show shiftGL k ^ toAdd a * (shiftGL k ^ (-toAdd a) * (g : LinearMap.GeneralLinearGroup k
          (ℤ →₀ k)) * (shiftGL k ^ (-toAdd a))⁻¹) * (shiftGL k ^ toAdd a)⁻¹ = g
        group)
      map_mul' := fun g h => Subtype.ext (by
        show shiftGL k ^ toAdd a * ((g : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) * h) *
            (shiftGL k ^ toAdd a)⁻¹ =
          (shiftGL k ^ toAdd a * g * (shiftGL k ^ toAdd a)⁻¹) *
            (shiftGL k ^ toAdd a * h * (shiftGL k ^ toAdd a)⁻¹)
        group) }
  map_one' := MulEquiv.ext fun g => Subtype.ext (by
    show shiftGL k ^ toAdd (1 : Multiplicative ℤ) * (g : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) *
      (shiftGL k ^ toAdd (1 : Multiplicative ℤ))⁻¹ = g
    rw [toAdd_one, zpow_zero, one_mul, inv_one, mul_one])
  map_mul' a b := MulEquiv.ext fun g => Subtype.ext (by
    show shiftGL k ^ toAdd (a * b) * (g : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) *
        (shiftGL k ^ toAdd (a * b))⁻¹ =
      shiftGL k ^ toAdd a * (shiftGL k ^ toAdd b * g * (shiftGL k ^ toAdd b)⁻¹) *
        (shiftGL k ^ toAdd a)⁻¹
    rw [toAdd_mul, zpow_add]
    group)

variable (k) in
/-- **`GL_fin(ℤ, k) ⋊ ℤ`** (tex 1776–1779), with `ℤ` acting by the bilateral shift. -/
abbrev FinitaryShift : Type _ := GLfin k ⋊[shiftAction k] Multiplicative ℤ

end FinitaryGL

end GroupApproximation

open GroupApproximation

#audit_axioms GroupApproximation.FinitaryGL.hasFiniteMatrixSupport_iff
#audit_axioms GroupApproximation.FinitaryGL.supportedIn_inv
#audit_axioms GroupApproximation.FinitaryGL.conj_mem_GLfin
#audit_axioms GroupApproximation.FinitaryGL.shiftGL_zpow_apply
