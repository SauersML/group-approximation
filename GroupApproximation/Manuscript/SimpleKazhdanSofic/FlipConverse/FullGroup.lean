import Mathlib

/-!
# Flip converse, part 2: topological full groups

For a homeomorphism `T` of a topological space `X`, the *topological full group* `[[T]]` is the
group of homeomorphisms `g` of `X` for which there is a continuous `n : X → ℤ` with
`g x = T^{n(x)} x` for all `x` (`topologicalFullGroup`, carrier `IsInFullGroup T`).

* `[[T]]` is a subgroup: `1 = T^0`; if `g = T^n`, `h = T^m` then `g h = T^{n ∘ h + m}`; and
  `g⁻¹ y = T^{-n(g⁻¹ y)} y`.  All cocycles are continuous.
* `T ∈ [[T]]` with `n ≡ 1`, and `[[T⁻¹]] = [[T]]` via `n ↦ -n`.
* A conjugacy `h : X ≃ₜ Y`, `h ∘ T = R ∘ h`, induces `[[T]] ≃* [[R]]`, `g ↦ h g h⁻¹`, since
  `h (T^k x) = R^k (h x)` for all `k ∈ ℤ` (`apply_hpow_of_semiconj`).  Composing with
  `[[S⁻¹]] = [[S]]`, a flip conjugacy (`FlipConjugate`: conjugate to `S` or `S⁻¹`) gives
  `[[T]] ≅ [[S]]` (`nonempty_mulEquiv_of_flipConjugate`).  This is the forward implication of the
  printed sentence for topological full groups.

Dynamical preliminaries.

* `IsAperiodic T`: `T^p x = x` implies `p = 0`; then `k ↦ T^k x` is injective.
* `IsMinimalHomeo T`: every orbit is dense.  If `X` is Hausdorff and infinite, a minimal `T` is
  aperiodic: a periodic orbit `{T^m x | 0 ≤ m < |p|}` is finite, hence closed, hence all of `X`.
* A nonempty perfect T₁ space is infinite (a finite T₁ space is discrete).
* If `n : X → ℤ` is continuous then `x ↦ T^{n(x)} x` is continuous: `n` is locally constant.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

variable {X : Type*} [TopologicalSpace X]

theorem homeoPow_add (T : X ≃ₜ X) (a b : ℤ) (x : X) :
    (T ^ (a + b)) x = (T ^ a) ((T ^ b) x) := by
  rw [zpow_add, Homeomorph.mul_apply]

theorem homeoPow_zero (T : X ≃ₜ X) (x : X) : (T ^ (0 : ℤ)) x = x := by
  rw [zpow_zero, Homeomorph.one_apply]

theorem homeoPow_one (T : X ≃ₜ X) (x : X) : (T ^ (1 : ℤ)) x = T x := by
  rw [zpow_one]

theorem homeoPow_neg_one (T : X ≃ₜ X) (x : X) : (T ^ (-1 : ℤ)) x = T.symm x := by
  rw [zpow_neg_one, Homeomorph.inv_apply]

/-- No periodic points. -/
def IsAperiodic (T : X ≃ₜ X) : Prop := ∀ (x : X) (p : ℤ), (T ^ p) x = x → p = 0

/-- Every orbit is dense. -/
def IsMinimalHomeo (T : X ≃ₜ X) : Prop := ∀ x : X, Dense (Set.range fun n : ℤ => (T ^ n) x)

theorem zpow_apply_injective {T : X ≃ₜ X} (hT : IsAperiodic T) {a b : ℤ} {x : X}
    (h : (T ^ a) x = (T ^ b) x) : a = b := by
  have hx : (T ^ (-b + a)) x = x := by
    rw [homeoPow_add, h, ← homeoPow_add, neg_add_cancel, homeoPow_zero]
  have := hT x _ hx
  omega

theorem zpow_apply_eq_self_of_apply_eq_self {g : X ≃ₜ X} {x : X} (hg : g x = x) (n : ℤ) :
    (g ^ n) x = x := by
  let S : Subgroup (X ≃ₜ X) :=
    { carrier := {f | f x = x}
      mul_mem' := fun {a b} ha hb => by
        have ha' : a x = x := ha
        have hb' : b x = x := hb
        show a (b x) = x
        rw [hb', ha']
      one_mem' := by
        show (1 : X ≃ₜ X) x = x
        rfl
      inv_mem' := fun {a} ha => by
        have ha' : a x = x := ha
        show a.symm x = x
        exact a.injective (by rw [Homeomorph.apply_symm_apply]; exact ha'.symm) }
  have hgS : g ∈ S := hg
  exact zpow_mem hgS n

theorem isAperiodic_of_isMinimalHomeo [T2Space X] [Infinite X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) : IsAperiodic T := by
  intro x p hp
  by_contra hp0
  have hsub : Set.range (fun n : ℤ => (T ^ n) x) ⊆
      (fun m : ℕ => (T ^ (m : ℤ)) x) '' (Finset.range p.natAbs : Set ℕ) := by
    rintro _ ⟨n, rfl⟩
    have h1 := Int.emod_nonneg n hp0
    have h2 := Int.emod_lt n hp0
    refine ⟨(n % p).toNat, ?_, ?_⟩
    · have h3 : (((n % p).toNat : ℕ) : ℤ) < ((p.natAbs : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg h1]
        exact h2
      simp only [Finset.coe_range, Set.mem_Iio]
      exact_mod_cast h3
    · have hfix := zpow_apply_eq_self_of_apply_eq_self hp (n / p)
      show (T ^ ((n % p).toNat : ℤ)) x = (T ^ n) x
      rw [Int.toNat_of_nonneg h1]
      rw [show (T ^ n) x = (T ^ (n % p + n / p * p)) x by rw [Int.emod_add_ediv_mul]]
      rw [homeoPow_add T (n % p) (n / p * p), zpow_mul', hfix]
  have hfin : (Set.range fun n : ℤ => (T ^ n) x).Finite :=
    ((Finset.range p.natAbs).finite_toSet.image _).subset hsub
  have huniv : Set.range (fun n : ℤ => (T ^ n) x) = Set.univ := by
    have hd := (hT x).closure_eq
    rwa [hfin.isClosed.closure_eq] at hd
  have hunivfin : (Set.univ : Set X).Finite := by
    rw [← huniv]
    exact hfin
  exact Set.infinite_univ hunivfin

theorem infinite_of_perfectSpace [T1Space X] [PerfectSpace X] [Nonempty X] : Infinite X := by
  by_contra h
  haveI : Finite X := not_infinite_iff_finite.1 h
  haveI : DiscreteTopology X := Finite.instDiscreteTopology
  obtain ⟨x⟩ := ‹Nonempty X›
  exact not_isOpen_singleton x (isOpen_discrete {x})

theorem continuous_hpow_apply (T : X ≃ₜ X) {n : X → ℤ} (hn : Continuous n) :
    Continuous fun x => (T ^ n x) x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hopen : IsOpen (n ⁻¹' {n x}) := hn.isOpen_preimage _ (isOpen_discrete _)
  refine ((T ^ n x).continuous.continuousAt).congr ?_
  refine Filter.eventually_of_mem (hopen.mem_nhds (Set.mem_preimage.2 (Set.mem_singleton _)))
    fun y hy => ?_
  have hy' : n y = n x := hy
  show (T ^ n x) y = (T ^ n y) y
  rw [hy']

theorem apply_hpow_of_semiconj {Y : Type*} [TopologicalSpace Y] {T : X ≃ₜ X} {S : Y ≃ₜ Y}
    (f : X → Y) (hf : ∀ x, f (T x) = S (f x)) (k : ℤ) (x : X) :
    f ((T ^ k) x) = (S ^ k) (f x) := by
  have hf' : ∀ x, f (T.symm x) = S.symm (f x) := fun x =>
    S.injective (by rw [← hf, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply])
  induction k generalizing x with
  | zero => rw [homeoPow_zero, homeoPow_zero]
  | succ i ih =>
    rw [homeoPow_add T (i : ℤ) 1, homeoPow_one T, ih, hf, homeoPow_add S (i : ℤ) 1,
      homeoPow_one S]
  | pred i ih =>
    rw [sub_eq_add_neg, homeoPow_add T (-(i : ℤ)) (-1), homeoPow_neg_one T, ih, hf',
      homeoPow_add S (-(i : ℤ)) (-1), homeoPow_neg_one S]

/-- `g x = T^{n(x)} x` for a continuous cocycle `n`. -/
def IsInFullGroup (T g : X ≃ₜ X) : Prop :=
  ∃ n : X → ℤ, Continuous n ∧ ∀ x, g x = (T ^ n x) x

theorem isInFullGroup_one (T : X ≃ₜ X) : IsInFullGroup T 1 := by
  refine ⟨fun _ => 0, continuous_const, fun x => ?_⟩
  show (1 : X ≃ₜ X) x = (T ^ (0 : ℤ)) x
  rw [homeoPow_zero, Homeomorph.one_apply]

theorem IsInFullGroup.mul {T g h : X ≃ₜ X} (hg : IsInFullGroup T g) (hh : IsInFullGroup T h) :
    IsInFullGroup T (g * h) := by
  obtain ⟨n, hn, hgn⟩ := hg
  obtain ⟨m, hm, hhm⟩ := hh
  refine ⟨fun x => n (h x) + m x, (hn.comp h.continuous).add hm, fun x => ?_⟩
  show g (h x) = (T ^ (n (h x) + m x)) x
  rw [homeoPow_add, ← hhm, ← hgn]

theorem IsInFullGroup.inv {T g : X ≃ₜ X} (hg : IsInFullGroup T g) : IsInFullGroup T g⁻¹ := by
  obtain ⟨n, hn, hgn⟩ := hg
  refine ⟨fun y => -n (g.symm y), (hn.comp g.symm.continuous).neg, fun y => ?_⟩
  show g.symm y = (T ^ (-n (g.symm y))) y
  calc g.symm y = (T ^ (-n (g.symm y) + n (g.symm y))) (g.symm y) := by
          rw [neg_add_cancel, homeoPow_zero]
    _ = (T ^ (-n (g.symm y))) ((T ^ n (g.symm y)) (g.symm y)) := homeoPow_add _ _ _ _
    _ = (T ^ (-n (g.symm y))) (g (g.symm y)) := by rw [← hgn]
    _ = (T ^ (-n (g.symm y))) y := by rw [Homeomorph.apply_symm_apply]

/-- The topological full group `[[T]]`. -/
def topologicalFullGroup (T : X ≃ₜ X) : Subgroup (X ≃ₜ X) where
  carrier := {g | IsInFullGroup T g}
  mul_mem' {a b} ha hb :=
    IsInFullGroup.mul (show IsInFullGroup T a from ha) (show IsInFullGroup T b from hb)
  one_mem' := isInFullGroup_one T
  inv_mem' {a} ha := IsInFullGroup.inv (show IsInFullGroup T a from ha)

theorem mem_topologicalFullGroup {T g : X ≃ₜ X} :
    g ∈ topologicalFullGroup T ↔ IsInFullGroup T g :=
  Iff.rfl

theorem self_mem_topologicalFullGroup (T : X ≃ₜ X) : T ∈ topologicalFullGroup T := by
  refine mem_topologicalFullGroup.2 ⟨fun _ => 1, continuous_const, fun x => ?_⟩
  show T x = (T ^ (1 : ℤ)) x
  rw [homeoPow_one]

theorem isInFullGroup_inv_iff {T g : X ≃ₜ X} : IsInFullGroup T⁻¹ g ↔ IsInFullGroup T g := by
  constructor
  · rintro ⟨n, hn, hgn⟩
    refine ⟨fun x => -n x, hn.neg, fun x => ?_⟩
    show g x = (T ^ (-n x)) x
    rw [hgn, inv_zpow']
  · rintro ⟨n, hn, hgn⟩
    refine ⟨fun x => -n x, hn.neg, fun x => ?_⟩
    show g x = (T⁻¹ ^ (-n x)) x
    rw [hgn, inv_zpow', neg_neg]

theorem topologicalFullGroup_inv (T : X ≃ₜ X) :
    topologicalFullGroup T⁻¹ = topologicalFullGroup T :=
  Subgroup.ext fun _ => isInFullGroup_inv_iff

section Conjugacy

variable {Y : Type*} [TopologicalSpace Y]

theorem symm_semiconj {T : X ≃ₜ X} {R : Y ≃ₜ Y} (h : X ≃ₜ Y) (hTR : ∀ x, h (T x) = R (h x)) :
    ∀ y, h.symm (R y) = T (h.symm y) := fun y =>
  h.injective (by rw [hTR, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply])

theorem IsInFullGroup.conj {T g : X ≃ₜ X} {R : Y ≃ₜ Y} (h : X ≃ₜ Y)
    (hTR : ∀ x, h (T x) = R (h x)) (hg : IsInFullGroup T g) :
    IsInFullGroup R ((h.symm.trans g).trans h) := by
  obtain ⟨n, hn, hgn⟩ := hg
  refine ⟨fun y => n (h.symm y), hn.comp h.symm.continuous, fun y => ?_⟩
  show h (g (h.symm y)) = (R ^ n (h.symm y)) y
  rw [hgn, apply_hpow_of_semiconj h hTR, Homeomorph.apply_symm_apply]

/-- A conjugacy `h ∘ T = R ∘ h` induces `[[T]] ≃* [[R]]`, `g ↦ h g h⁻¹`. -/
def fullGroupMulEquiv {T : X ≃ₜ X} {R : Y ≃ₜ Y} (h : X ≃ₜ Y)
    (hTR : ∀ x, h (T x) = R (h x)) : topologicalFullGroup T ≃* topologicalFullGroup R where
  toFun g := ⟨(h.symm.trans g.1).trans h,
    mem_topologicalFullGroup.2 (IsInFullGroup.conj h hTR (mem_topologicalFullGroup.1 g.2))⟩
  invFun g := ⟨(h.symm.symm.trans g.1).trans h.symm,
    mem_topologicalFullGroup.2
      (IsInFullGroup.conj h.symm (symm_semiconj h hTR) (mem_topologicalFullGroup.1 g.2))⟩
  left_inv g := Subtype.ext <| Homeomorph.ext fun x => by
    show h.symm (h (g.1 (h.symm (h x)))) = g.1 x
    rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
  right_inv g := Subtype.ext <| Homeomorph.ext fun y => by
    show h (h.symm (g.1 (h (h.symm y)))) = g.1 y
    rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  map_mul' g₁ g₂ := Subtype.ext <| Homeomorph.ext fun y => by
    show h (g₁.1 (g₂.1 (h.symm y))) = h (g₁.1 (h.symm (h (g₂.1 (h.symm y)))))
    rw [Homeomorph.symm_apply_apply]

/-- `(X,T)` and `(Y,S)` are flip conjugate: conjugate to `S` or to `S⁻¹`. -/
def FlipConjugate (T : X ≃ₜ X) (S : Y ≃ₜ Y) : Prop :=
  ∃ h : X ≃ₜ Y, (∀ x, h (T x) = S (h x)) ∨ ∀ x, h (T x) = S.symm (h x)

theorem nonempty_mulEquiv_of_flipConjugate {T : X ≃ₜ X} {S : Y ≃ₜ Y}
    (hflip : FlipConjugate T S) :
    Nonempty (topologicalFullGroup T ≃* topologicalFullGroup S) := by
  obtain ⟨h, hTS | hTS⟩ := hflip
  · exact ⟨fullGroupMulEquiv h hTS⟩
  · exact ⟨(fullGroupMulEquiv (R := S⁻¹) h hTS).trans
      (MulEquiv.subgroupCongr (topologicalFullGroup_inv S))⟩

end Conjugacy

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
