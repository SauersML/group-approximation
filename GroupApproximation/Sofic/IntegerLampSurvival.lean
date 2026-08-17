import GroupApproximation.Sofic.LocallyFiniteMF
import GroupApproximation.Sofic.SoficMarkedCompression

/-!
# Integer lamps over the telescope survive: the MF half of the dichotomy

The collapse theorems kill finite-order lamps over a compressed Kazhdan
site space.  This module kernel-checks the survival half of that
spectral dichotomy at the layer where it is a theorem of pure group
theory: the restricted integer-lamp wreath over the telescope — the
infinite-cyclic analogue of the Clifford lamp kernel — is operator-MF
whenever the base group is residually finite and the compressing
endomorphism has finite-index range.

The mechanism is locality.  A finite subset of the wreath touches
finitely many lamps and finitely many telescope elements; the telescope
elements live in one level, the level has finite orbits on the site
space, and the orbit closure of the touched sites is a finite invariant
window.  The subgroup of lamps supported in the window over the level
is then residually finite outright: an element with nontrivial base
part dies in a finite quotient of the level, and an element that is a
pure lamp configuration survives reduction of its integer values modulo
a large integer inside the finite wreath over the window.  Exhaustion
by residually finite subgroups gives LEF, and LEF gives operator-MF.

The full group `W_Z` — with the compressing shift adjoined — is NOT
reached by this argument, and cannot be: adjoining the shift destroys
the local finiteness of orbits, exactly as it does on the Clifford
side.  Its MF-ness is the slow-bump corona construction of the research
notes and remains outside the formal development; this module supplies
the largest layer on which the survival statement is a locality fact.
-/

namespace GroupApproximation
namespace IntegerLampSurvival

universe u v

/-! ## Coefficient-generic lamp groups and their permutation action -/

section Lamps

variable {X : Type u} {M : Type*} [AddCommGroup M]

/-- The restricted lamp group with coefficient group `M`, written
multiplicatively so that it can feed a semidirect product. -/
abbrev Lamps (X : Type u) (M : Type v) [AddCommGroup M] : Type (max u v) :=
  Multiplicative (X →₀ M)

/-- The automorphism of the lamp group induced by one site permutation:
the configuration is precomposed with the inverse permutation. -/
def lampAutOf (e : Equiv.Perm X) : MulAut (Lamps X M) where
  toFun l := Multiplicative.ofAdd
    (Finsupp.equivMapDomain e (Multiplicative.toAdd l))
  invFun l := Multiplicative.ofAdd
    (Finsupp.equivMapDomain e.symm (Multiplicative.toAdd l))
  left_inv l := by
    apply Multiplicative.toAdd.injective
    ext x
    simp [Finsupp.equivMapDomain_apply]
  right_inv l := by
    apply Multiplicative.toAdd.injective
    ext x
    simp [Finsupp.equivMapDomain_apply]
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    ext x
    simp [Finsupp.equivMapDomain_apply, Finsupp.add_apply]

@[simp] theorem lampAutOf_apply_toAdd (e : Equiv.Perm X)
    (l : Lamps X M) (x : X) :
    Multiplicative.toAdd (lampAutOf e l) x =
      Multiplicative.toAdd l (e.symm x) := rfl

variable {H : Type u} [Group H]

/-- Permutations multiply as reversed composition, so their inverses
compose in the forward order; recorded once because `simp` cannot see
through the definitional unfolding. -/
@[simp] theorem perm_mul_symm_apply (e₁ e₂ : Equiv.Perm X) (x : X) :
    (e₁ * e₂).symm x = e₂.symm (e₁.symm x) := rfl

/-- The lamp action of a group acting on the sites by permutations. -/
def lampAut (ρ : H →* Equiv.Perm X) : H →* MulAut (Lamps X M) where
  toFun h := lampAutOf (ρ h)
  map_one' := by
    apply MulEquiv.ext
    intro l
    apply Multiplicative.toAdd.injective
    ext x
    rw [map_one]
    rfl
  map_mul' h h' := by
    apply MulEquiv.ext
    intro l
    apply Multiplicative.toAdd.injective
    ext x
    rw [map_mul]
    rfl

@[simp] theorem lampAut_apply_toAdd (ρ : H →* Equiv.Perm X) (h : H)
    (l : Lamps X M) (x : X) :
    Multiplicative.toAdd (lampAut ρ h l) x =
      Multiplicative.toAdd l ((ρ h).symm x) := rfl

/-- The restricted permutational lamp wreath. -/
abbrev LampWreath (M : Type v) [AddCommGroup M] {X H : Type u} [Group H]
    (ρ : H →* Equiv.Perm X) : Type (max u v) :=
  Lamps X M ⋊[lampAut ρ] H

end Lamps

/-! ## Invariant windows -/

section Windows

variable {X H : Type u} [Group H] (ρ : H →* Equiv.Perm X)

/-- A set of sites is invariant under a subgroup when the subgroup's
permutations map it into itself. -/
def IsInvariant (H₀ : Subgroup H) (S : Set X) : Prop :=
  ∀ h ∈ H₀, ∀ x ∈ S, ρ h x ∈ S

/-- Two-sided form: an invariant set is mapped onto itself, so the
complement is preserved as well. -/
theorem IsInvariant.notMem {H₀ : Subgroup H} {S : Set X}
    (hS : IsInvariant ρ H₀ S) {h : H} (hh : h ∈ H₀) {x : X}
    (hx : x ∉ S) : ρ h x ∉ S := by
  intro hmem
  apply hx
  have h2 := hS h⁻¹ (H₀.inv_mem hh) _ hmem
  rw [map_inv] at h2
  have h3 : (ρ h)⁻¹ (ρ h x) = x := Equiv.symm_apply_apply (ρ h) x
  rwa [h3] at h2

theorem IsInvariant.symm_notMem {H₀ : Subgroup H} {S : Set X}
    (hS : IsInvariant ρ H₀ S) {h : H} (hh : h ∈ H₀) {x : X}
    (hx : x ∉ S) : (ρ h).symm x ∉ S := by
  intro hmem
  apply hx
  have h2 := hS h hh _ hmem
  rwa [Equiv.apply_symm_apply] at h2

/-- The invariance condition in the `iff` form the subtype permutation
constructor consumes. -/
theorem IsInvariant.mem_iff {H₀ : Subgroup H} {S : Set X}
    (hS : IsInvariant ρ H₀ S) {h : H} (hh : h ∈ H₀) (x : X) :
    ρ h x ∈ S ↔ x ∈ S := by
  constructor
  · intro hmem
    by_contra hx
    exact hS.notMem ρ hh hx hmem
  · intro hx
    exact hS h hh x hx

/-- The window subgroup: lamp configurations vanishing outside an
invariant window, over a chosen subgroup of the acting group. -/
def windowSubgroup {M : Type*} [AddCommGroup M] (H₀ : Subgroup H)
    (S : Set X) (hS : IsInvariant ρ H₀ S) :
    Subgroup (LampWreath M ρ) where
  carrier := {w | (∀ x, x ∉ S →
    Multiplicative.toAdd w.left x = 0) ∧ w.right ∈ H₀}
  one_mem' := ⟨fun x _ ↦ rfl, H₀.one_mem⟩
  mul_mem' {a b} ha hb := by
    refine ⟨?_, H₀.mul_mem ha.2 hb.2⟩
    intro x hx
    rw [SemidirectProduct.mul_left]
    show Multiplicative.toAdd a.left x +
      Multiplicative.toAdd (lampAut ρ a.right b.left) x = 0
    rw [ha.1 x hx, lampAut_apply_toAdd,
      hb.1 _ (hS.symm_notMem ρ ha.2 hx), add_zero]
  inv_mem' {a} ha := by
    refine ⟨?_, H₀.inv_mem ha.2⟩
    intro x hx
    show Multiplicative.toAdd (lampAut ρ a.right⁻¹ a.left⁻¹) x = 0
    rw [lampAut_apply_toAdd]
    show -(Multiplicative.toAdd a.left ((ρ a.right⁻¹).symm x)) = 0
    rw [map_inv]
    have hxx : ((ρ a.right)⁻¹).symm x = ρ a.right x := rfl
    rw [hxx, ha.1 _ (hS.notMem ρ ha.2 hx), neg_zero]

theorem mem_windowSubgroup {M : Type*} [AddCommGroup M]
    {H₀ : Subgroup H} {S : Set X} {hS : IsInvariant ρ H₀ S}
    {w : LampWreath M ρ} :
    w ∈ windowSubgroup ρ H₀ S hS ↔
      (∀ x, x ∉ S → Multiplicative.toAdd w.left x = 0) ∧
        w.right ∈ H₀ :=
  Iff.rfl

end Windows

/-! ## Residual finiteness of a window subgroup -/

section WindowRF

variable {X H : Type u} [Group H] (ρ : H →* Equiv.Perm X)

/-- The finite lamp wreath over a finite invariant window, with integer
values reduced modulo `N`: the finite target for the lamp-separating
homomorphism. -/
theorem finite_lampWreath_perm (S : Set X) (hSfin : S.Finite) (N : ℕ)
    [NeZero N] :
    Finite (LampWreath (ZMod N)
      (MonoidHom.id (Equiv.Perm (Subtype (· ∈ S))))) := by
  haveI : Finite (Subtype (· ∈ S)) := hSfin.to_subtype
  haveI hlamps : Finite (Subtype (· ∈ S) →₀ ZMod N) :=
    Finite.of_equiv _ Finsupp.equivFunOnFinite.symm
  haveI hperm : Finite (Equiv.Perm (Subtype (· ∈ S))) := by
    refine Finite.of_injective
      (fun e : Equiv.Perm (Subtype (· ∈ S)) ↦ (⇑e : _ → _)) ?_
    intro e₁ e₂ h
    exact Equiv.ext (congrFun h)
  refine Finite.of_injective
    (fun w : LampWreath (ZMod N)
        (MonoidHom.id (Equiv.Perm (Subtype (· ∈ S)))) ↦
      (w.left, w.right)) ?_
  intro a b hab
  exact SemidirectProduct.ext (congrArg Prod.fst hab)
    (congrArg Prod.snd hab)

/-- Restriction of an integer lamp configuration to a window, with
values reduced modulo `N`. -/
noncomputable def restrictLamp (S : Set X) (N : ℕ) [NeZero N] (l : X →₀ ℤ) :
    Subtype (· ∈ S) →₀ ZMod N :=
  Finsupp.mapRange (Int.cast : ℤ → ZMod N) (Int.cast_zero)
    (Finsupp.subtypeDomain (· ∈ S) l)

@[simp] theorem restrictLamp_apply (S : Set X) (N : ℕ) [NeZero N]
    (l : X →₀ ℤ) (x : Subtype (· ∈ S)) :
    restrictLamp S N l x = ((l x.1 : ℤ) : ZMod N) := by
  rw [restrictLamp, Finsupp.mapRange_apply, Finsupp.subtypeDomain_apply]

theorem restrictLamp_add (S : Set X) (N : ℕ) [NeZero N] (l l' : X →₀ ℤ) :
    restrictLamp S N (l + l') =
      restrictLamp S N l + restrictLamp S N l' := by
  ext x
  rw [Finsupp.add_apply, restrictLamp_apply, restrictLamp_apply,
    restrictLamp_apply, Finsupp.add_apply, Int.cast_add]

/-- The window homomorphism: restrict the lamps to the finite window,
reduce their values modulo `N`, and restrict the permutation part to
the window.  Everything a pure lamp configuration knows inside the
window survives into a finite group. -/
noncomputable def windowHom {H₀ : Subgroup H} {S : Set X} (hS : IsInvariant ρ H₀ S)
    (N : ℕ) [NeZero N] :
    (windowSubgroup ρ (M := ℤ) H₀ S hS) →*
      LampWreath (ZMod N)
        (MonoidHom.id (Equiv.Perm (Subtype (· ∈ S)))) where
  toFun w :=
    ⟨Multiplicative.ofAdd
        (restrictLamp S N (Multiplicative.toAdd w.1.left)),
      (ρ w.1.right).subtypePerm fun x ↦ hS.mem_iff ρ w.2.2 x⟩
  map_one' := by
    refine SemidirectProduct.ext ?_ ?_
    · apply Multiplicative.toAdd.injective
      ext x
      show (((0 : X →₀ ℤ) x.1 : ℤ) : ZMod N) = 0
      simp
    · apply Equiv.ext
      intro x
      apply Subtype.ext
      show ρ 1 x.1 = x.1
      rw [map_one]
      rfl
  map_mul' a b := by
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.mul_left]
      apply Multiplicative.toAdd.injective
      ext x
      show restrictLamp S N
          (Multiplicative.toAdd ((a.1 * b.1 : LampWreath ℤ ρ).left)) x =
        (restrictLamp S N (Multiplicative.toAdd a.1.left) +
          Finsupp.equivMapDomain
            ((ρ a.1.right).subtypePerm fun y ↦ hS.mem_iff ρ a.2.2 y)
            (restrictLamp S N (Multiplicative.toAdd b.1.left))) x
      rw [SemidirectProduct.mul_left]
      show restrictLamp S N (Multiplicative.toAdd a.1.left +
          Multiplicative.toAdd (lampAut ρ a.1.right b.1.left)) x = _
      rw [restrictLamp_add, Finsupp.add_apply, Finsupp.add_apply,
        Finsupp.equivMapDomain_apply, restrictLamp_apply,
        restrictLamp_apply, restrictLamp_apply, lampAut_apply_toAdd]
      rfl
    · apply Equiv.ext
      intro x
      apply Subtype.ext
      show ρ ((a.1 * b.1 : LampWreath ℤ ρ).right) x.1 = _
      rw [SemidirectProduct.mul_right, map_mul]
      rfl

/-- **A window subgroup over a residually finite level is residually
finite.**  Nontrivial base parts die in a finite quotient of the level;
nontrivial pure lamp configurations die in the finite window wreath
after reduction modulo an integer exceeding the lamp value. -/
theorem residuallyFinite_windowSubgroup (H₀ : Subgroup H)
    [Group.ResiduallyFinite H₀] {S : Set X} (hSfin : S.Finite)
    (hS : IsInvariant ρ H₀ S) :
    Group.ResiduallyFinite (windowSubgroup ρ (M := ℤ) H₀ S hS) := by
  classical
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro w hw
  by_cases hr : w.1.right = 1
  · -- pure lamp configuration: reduce modulo a large integer
    have hleft : w.1.left ≠ 1 := by
      intro hcon
      exact hw (Subtype.ext (SemidirectProduct.ext hcon hr))
    have hadd : Multiplicative.toAdd w.1.left ≠ 0 := fun hcon ↦
      hleft (Multiplicative.toAdd.injective hcon)
    obtain ⟨x₀, hx₀⟩ :=
      Finsupp.support_nonempty_iff.mpr hadd
    have hval : Multiplicative.toAdd w.1.left x₀ ≠ 0 :=
      Finsupp.mem_support_iff.mp hx₀
    set v : ℤ := Multiplicative.toAdd w.1.left x₀ with hv
    set N : ℕ := v.natAbs + 1 with hN
    haveI : NeZero N := ⟨Nat.succ_ne_zero _⟩
    haveI := finite_lampWreath_perm S hSfin N
    have hx₀S : x₀ ∈ S := by
      by_contra hx
      exact hval (w.2.1 x₀ hx)
    refine ⟨LampWreath (ZMod N)
      (MonoidHom.id (Equiv.Perm (Subtype (· ∈ S)))), inferInstance,
      inferInstance, windowHom ρ hS N, ?_⟩
    intro hcon
    have hleft2 := congrArg SemidirectProduct.left hcon
    have h1 : restrictLamp S N (Multiplicative.toAdd w.1.left)
        ⟨x₀, hx₀S⟩ = 0 := by
      have h2 : Multiplicative.toAdd ((windowHom ρ hS N w).left)
          ⟨x₀, hx₀S⟩ = Multiplicative.toAdd
            ((1 : LampWreath (ZMod N)
              (MonoidHom.id (Equiv.Perm (Subtype (· ∈ S))))).left)
            ⟨x₀, hx₀S⟩ := by
        rw [hleft2]
      exact h2
    rw [restrictLamp_apply] at h1
    have hzero : ((v : ℤ) : ZMod N) = 0 := h1
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzero
    have hdvd : N ∣ v.natAbs :=
      Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hzero)
    have habs : v.natAbs = 0 :=
      Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    exact hval (Int.natAbs_eq_zero.mp habs)
  · -- nontrivial base part: kill it in a finite quotient of the level
    let π : (windowSubgroup ρ (M := ℤ) H₀ S hS) →* H₀ :=
      { toFun := fun a ↦ ⟨a.1.right, a.2.2⟩
        map_one' := rfl
        map_mul' := fun a b ↦
          Subtype.ext (SemidirectProduct.mul_right a.1 b.1) }
    have hπw : π w ≠ 1 := by
      intro hcon
      exact hr (congrArg Subtype.val hcon)
    obtain ⟨K, hnotmem⟩ :=
      Group.exists_finiteIndexNormalSubgroup_notMem (π w) hπw
    letI := K.isNormal'
    letI := K.isFiniteIndex'
    haveI : Finite (H₀ ⧸ K.toSubgroup) :=
      Subgroup.finite_quotient_of_finiteIndex
    refine ⟨H₀ ⧸ K.toSubgroup, inferInstance, inferInstance,
      (QuotientGroup.mk' K.toSubgroup).comp π, ?_⟩
    intro hcon
    exact hnotmem ((QuotientGroup.eq_one_iff (π w)).mp hcon)

end WindowRF

/-! ## The local criterion -/

section Main

variable {X H : Type u} [Group H]

/-- **Locally finite orbits over locally residually finite levels make
the integer-lamp wreath operator-MF.**  Every finite subset of the
wreath lies in a window subgroup, and window subgroups are residually
finite. -/
theorem isOperatorMF_lampWreath [Countable X] [Countable H]
    (ρ : H →* Equiv.Perm X)
    (hloc : ∀ F : Finset H, ∃ H₀ : Subgroup H,
      (∀ h ∈ F, h ∈ H₀) ∧ Group.ResiduallyFinite H₀ ∧
        ∀ x : X, (Set.range fun h₀ : H₀ ↦ ρ h₀ x).Finite) :
    IsOperatorMF (LampWreath ℤ ρ) := by
  classical
  haveI : Countable (Lamps X ℤ) :=
    inferInstanceAs (Countable (X →₀ ℤ))
  haveI : Countable (LampWreath ℤ ρ) :=
    Function.Injective.countable
      (f := fun w : LampWreath ℤ ρ ↦ (w.left, w.right))
      fun a b hab ↦ SemidirectProduct.ext
        (congrArg Prod.fst hab) (congrArg Prod.snd hab)
  apply isOperatorMF_of_forall_finset_residuallyFinite
  intro s
  obtain ⟨H₀, hF, hRF, horb⟩ :=
    hloc (s.image SemidirectProduct.right)
  set S : Set X := ⋃ w ∈ (s : Set (LampWreath ℤ ρ)),
    ⋃ x ∈ (↑(Multiplicative.toAdd
      (SemidirectProduct.left w)).support : Set X),
      Set.range fun h₀ : H₀ ↦ ρ h₀ x with hSdef
  have hSfin : S.Finite := by
    refine Set.Finite.biUnion s.finite_toSet fun w _ ↦ ?_
    exact Set.Finite.biUnion (Finset.finite_toSet _) fun x _ ↦ horb x
  have hSinv : IsInvariant ρ H₀ S := by
    intro h hh y hy
    rw [hSdef, Set.mem_iUnion₂] at hy
    obtain ⟨w, hw, hy⟩ := hy
    rw [Set.mem_iUnion₂] at hy
    obtain ⟨x, hx, hy⟩ := hy
    obtain ⟨h₀, rfl⟩ := hy
    rw [hSdef, Set.mem_iUnion₂]
    refine ⟨w, hw, ?_⟩
    rw [Set.mem_iUnion₂]
    refine ⟨x, hx, ⟨⟨h * h₀, H₀.mul_mem hh h₀.2⟩, ?_⟩⟩
    show ρ (h * h₀) x = ρ h (ρ h₀ x)
    rw [map_mul]
    rfl
  haveI := hRF
  refine ⟨windowSubgroup ρ H₀ S hSinv, ?_,
    residuallyFinite_windowSubgroup ρ H₀ hSfin hSinv⟩
  intro w hw
  refine (mem_windowSubgroup ρ).mpr ⟨?_, ?_⟩
  · intro x hx
    by_contra hval
    apply hx
    rw [hSdef, Set.mem_iUnion₂]
    refine ⟨w, hw, ?_⟩
    rw [Set.mem_iUnion₂]
    refine ⟨x, Finsupp.mem_support_iff.mpr hval,
      ⟨(1 : H₀), ?_⟩⟩
    show ρ 1 x = x
    rw [map_one]
    rfl
  · exact hF w.right (Finset.mem_image_of_mem _ hw)

end Main

/-! ## The telescope instance: the survival half of the dichotomy -/

section Telescope

open MappingTelescope MarkedCompression SemidirectProduct

variable {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- The site action of the whole telescope on the marked coset space:
the level actions of `SoficMarkedCompression.levelSiteAction`, assembled
over all levels. -/
def telescopeSiteAction : Telescope α hα →* Equiv.Perm (Cosets α hα) :=
  (MulAction.toPermHom (Vertical α hα) (Cosets α hα)).comp
    (inl : Telescope α hα →* Vertical α hα)

/-- **Integer lamps over the telescope form an operator-MF group.**
This is the survival half of the lamp-spectrum dichotomy at the
telescope layer: with residually finite base and finite-index
compression, the infinite-cyclic lamp wreath over the compressed site
space embeds in a corona, while its finite-order counterpart is killed
by the collapse theorems.  The compressing shift itself is deliberately
absent; adjoining it leaves the locality argument, and its MF-ness is
the analytic slow-bump construction outside the formal development. -/
theorem isOperatorMF_integerLampTelescope [Countable Γ]
    [Group.ResiduallyFinite Γ] [α.range.FiniteIndex] :
    IsOperatorMF (LampWreath ℤ (telescopeSiteAction α hα)) := by
  apply isOperatorMF_lampWreath
  intro F
  choose lvl elt hrepr using exists_level_repr α hα
  refine ⟨(level α hα (F.sup lvl)).range, ?_, ?_, ?_⟩
  · intro g hg
    have hle : lvl g ≤ F.sup lvl := Finset.le_sup hg
    have hmem := level_mem_range_of_le α hα hle (elt g)
    rwa [hrepr g] at hmem
  · have hequiv : Γ ≃* ((level α hα (F.sup lvl)).range) :=
      MonoidHom.ofInjective (level_injective α hα _)
    exact residuallyFinite_of_injective hequiv.symm.toMonoidHom
      hequiv.symm.injective
  · intro x
    exact SoficMarkedCompression.finite_levelSiteAction_orbit
      α hα (F.sup lvl) x

end Telescope

end IntegerLampSurvival
end GroupApproximation
