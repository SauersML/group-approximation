import GroupApproximation.Sofic.SoficMarkedCompression
import GroupApproximation.Sofic.CommutingLampCollapse
import GroupApproximation.Sofic.LiteralWitnessConsequences
import GroupApproximation.Sofic.LiteralBaseDoublingIndex
import GroupApproximation.Algebra.CountableInstances

/-!
# The sign-free quotient is sofic

The commuting-lamp quotient of the marked-compression ambient group —
the witness group modulo its central Clifford sign — is already known
to be non-MF (`Sofic/CommutingLampCollapse`).  This file proves that it
is SOFIC, so the sign-free quotient is an explicit finitely generated
sofic group that is not MF.

The route has three layers.  First, killing the sign abelianizes the
lamp kernel: the presented Clifford group modulo its sign is identified
with the elementary abelian mod-two lamp group `Cosets →₀ ZMod 2`.  The
identification needs no normal-form theory: the mod-two model is
presented by the same generators through the universal property, and a
section built from `Finsupp.liftAddHom` pins the kernel to the sign's
powers.  Second, the ambient group modulo the sign is therefore the
mod-two lamp group under the same vertical action.  Third, the sofic
permanence pipeline of `Sofic/SoficMarkedCompression` replays verbatim
for mod-two lamps: finite site orbits of a telescope level give finite
invariant lamp windows, the local finite-kernel criterion applies, and
the integer shift is adjoined by the sofic-by-cyclic extension theorem.
-/

namespace GroupApproximation
namespace CommutingLampQuotientSofic

open CliffordLamp MappingTelescope MarkedCompression SemidirectProduct
open scoped commutatorElement

universe w

/-! ## The mod-two lamp model -/

/-- The elementary abelian mod-two lamp group over a site set. -/
abbrev ModTwoLamp (X : Type w) : Type w := Multiplicative (X →₀ ZMod 2)

variable {X : Type w}

/-- Generator induction for the mod-two lamp group: a subgroup containing
every single-site lamp contains everything. -/
theorem mem_subgroup_of_single_mem (P : Subgroup (ModTwoLamp X))
    (hsingle : ∀ x : X,
      Multiplicative.ofAdd (Finsupp.single x (1 : ZMod 2)) ∈ P)
    (f : X →₀ ZMod 2) : Multiplicative.ofAdd f ∈ P := by
  classical
  refine Finsupp.induction f P.one_mem ?_
  intro a b f _ hb ih
  have hsplit : Multiplicative.ofAdd (Finsupp.single a b + f) =
      Multiplicative.ofAdd (Finsupp.single a b) *
        Multiplicative.ofAdd f := rfl
  rw [hsplit]
  refine P.mul_mem ?_ ih
  have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hcases b with rfl | rfl
  · exact absurd rfl hb
  · exact hsingle a

/-- The finite window of lamps supported inside a fixed finite site set. -/
def finsuppWindow (s : Finset X) : Subgroup (ModTwoLamp X) where
  carrier := {f | (Multiplicative.toAdd f).support ⊆ s}
  one_mem' := by
    show (Multiplicative.toAdd (1 : ModTwoLamp X)).support ⊆ s
    show (0 : X →₀ ZMod 2).support ⊆ s
    rw [Finsupp.support_zero]
    exact Finset.empty_subset s
  mul_mem' := by
    classical
    intro a b ha hb
    show (Multiplicative.toAdd a + Multiplicative.toAdd b).support ⊆ s
    refine Finsupp.support_add.trans ?_
    exact Finset.union_subset ha hb
  inv_mem' := by
    intro a ha
    show (-(Multiplicative.toAdd a)).support ⊆ s
    rw [Finsupp.support_neg]
    exact ha

theorem finite_finsuppWindow (s : Finset X) : Finite (finsuppWindow s) := by
  classical
  have hinj : Function.Injective
      (fun p : finsuppWindow s ↦
        (fun i : s ↦ Multiplicative.toAdd (p : ModTwoLamp X) i)) := by
    intro p q hpq
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    ext x
    by_cases hx : x ∈ s
    · exact congrFun hpq ⟨x, hx⟩
    · have hp : x ∉ (Multiplicative.toAdd (p : ModTwoLamp X)).support :=
        fun hmem ↦ hx (p.2 hmem)
      have hq : x ∉ (Multiplicative.toAdd (q : ModTwoLamp X)).support :=
        fun hmem ↦ hx (q.2 hmem)
      rw [Finsupp.notMem_support_iff.mp hp,
        Finsupp.notMem_support_iff.mp hq]
  exact Finite.of_injective _ hinj

/-- The mod-two lamp group is locally finite. -/
theorem isLocallyFiniteGroup_modTwoLamp :
    IsLocallyFiniteGroup (ModTwoLamp X) := by
  classical
  intro s
  refine ⟨finsuppWindow
    (s.sup fun f ↦ (Multiplicative.toAdd f).support), ?_, ?_⟩
  · exact finite_finsuppWindow _
  · intro g hg
    show (Multiplicative.toAdd g).support ⊆ _
    have := Finset.le_sup (f := fun f : ModTwoLamp X ↦
      (Multiplicative.toAdd f).support) hg
    exact this

/-- A permutation of the sites acts on mod-two lamps by relabeling. -/
noncomputable def permMulEquiv (σ : Equiv.Perm X) :
    ModTwoLamp X ≃* ModTwoLamp X :=
  AddEquiv.toMultiplicative (Finsupp.domCongr σ)

@[simp] theorem permMulEquiv_apply_toAdd (σ : Equiv.Perm X)
    (f : ModTwoLamp X) (x : X) :
    Multiplicative.toAdd (permMulEquiv σ f) x =
      Multiplicative.toAdd f (σ.symm x) := by
  show (Finsupp.equivMapDomain σ (Multiplicative.toAdd f)) x =
    Multiplicative.toAdd f (σ.symm x)
  rw [Finsupp.equivMapDomain_apply]

/-- The relabeling action, as a homomorphism to the automorphisms. -/
noncomputable def permHomModTwo : Equiv.Perm X →* MulAut (ModTwoLamp X) where
  toFun := permMulEquiv
  map_one' := by
    apply MulEquiv.ext
    intro f
    apply Multiplicative.toAdd.injective
    ext x
    rw [permMulEquiv_apply_toAdd]
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro f
    apply Multiplicative.toAdd.injective
    ext x
    show Multiplicative.toAdd (permMulEquiv (σ * τ) f) x =
      Multiplicative.toAdd (permMulEquiv σ (permMulEquiv τ f)) x
    rw [permMulEquiv_apply_toAdd, permMulEquiv_apply_toAdd,
      permMulEquiv_apply_toAdd]
    have hsymm : (σ * τ)⁻¹ x = τ⁻¹ (σ⁻¹ x) := by
      rw [mul_inv_rev]
      rfl
    show Multiplicative.toAdd f ((σ * τ).symm x) = _
    show Multiplicative.toAdd f ((σ * τ)⁻¹ x) = _
    rw [hsymm]
    rfl

@[simp] theorem permHomModTwo_apply_single (σ : Equiv.Perm X) (x : X) :
    permHomModTwo σ
        (Multiplicative.ofAdd (Finsupp.single x (1 : ZMod 2))) =
      Multiplicative.ofAdd (Finsupp.single (σ x) (1 : ZMod 2)) := by
  show Multiplicative.ofAdd
      (Finsupp.equivMapDomain σ (Finsupp.single x (1 : ZMod 2))) = _
  rw [Finsupp.equivMapDomain_single]

/-- An action on sites induces the relabeling action on mod-two lamps. -/
noncomputable def finsuppActionHom {H : Type*} [Group H]
    (ρ : H →* Equiv.Perm X) :
    H →* MulAut (ModTwoLamp X) :=
  permHomModTwo.comp ρ

@[simp] theorem finsuppActionHom_apply_single {H : Type*} [Group H]
    (ρ : H →* Equiv.Perm X) (h : H) (x : X) :
    finsuppActionHom ρ h
        (Multiplicative.ofAdd (Finsupp.single x (1 : ZMod 2))) =
      Multiplicative.ofAdd (Finsupp.single (ρ h x) (1 : ZMod 2)) := by
  show permHomModTwo (ρ h)
      (Multiplicative.ofAdd (Finsupp.single x (1 : ZMod 2))) = _
  rw [permHomModTwo_apply_single]

/-- Finite site orbits give finite orbits on every mod-two lamp. -/
theorem finite_orbit_of_finite_site_orbits_modTwo {H : Type*} [Group H]
    (ρ : H →* Equiv.Perm X)
    (hsite : ∀ x : X, (Set.range fun h : H ↦ ρ h x).Finite)
    (n : ModTwoLamp X) :
    (Set.range fun h : H ↦ finsuppActionHom ρ h n).Finite := by
  classical
  let P := finiteOrbitSubgroup (finsuppActionHom ρ)
  have hmem : ∀ f : X →₀ ZMod 2, Multiplicative.ofAdd f ∈ P := by
    intro f
    apply mem_subgroup_of_single_mem
    intro x
    show (Set.range fun h : H ↦ finsuppActionHom ρ h
      (Multiplicative.ofAdd (Finsupp.single x 1))).Finite
    refine ((hsite x).image fun y : X ↦
      Multiplicative.ofAdd (Finsupp.single y (1 : ZMod 2))).subset ?_
    rintro _ ⟨h, rfl⟩
    refine ⟨ρ h x, ⟨⟨h, rfl⟩, ?_⟩⟩
    simp only [finsuppActionHom_apply_single]
  have hn : n ∈ P := by
    have := hmem (Multiplicative.toAdd n)
    exact this
  exact hn

/-- Finite site orbits give the finite invariant mod-two windows consumed
by the local semidirect permanence theorem. -/
theorem exists_finite_invariant_modTwo_subgroup {H : Type*} [Group H]
    (ρ : H →* Equiv.Perm X)
    (hsite : ∀ x : X, (Set.range fun h : H ↦ ρ h x).Finite)
    (F : Finset (ModTwoLamp X)) :
    ∃ K : Subgroup (ModTwoLamp X), Finite K ∧
      (∀ h : H, ∀ n ∈ K, finsuppActionHom ρ h n ∈ K) ∧
      ∀ n ∈ F, n ∈ K :=
  exists_finite_invariant_subgroup_of_finite_orbits
    (finsuppActionHom ρ) isLocallyFiniteGroup_modTwoLamp
    (finite_orbit_of_finite_site_orbits_modTwo ρ hsite) F

/-! ## Abelianization of the Clifford lamps -/

/-- The mod-two abelianization of the Clifford lamp group, through the
universal property of the presentation: the sign dies, each lamp becomes
the corresponding single-site flip. -/
noncomputable def toModTwo : CliffordLamp X →* ModTwoLamp X :=
  PresentedGroup.toGroup (f := Sum.elim
      (fun _ : Unit ↦ (1 : ModTwoLamp X))
      (fun x : X ↦ Multiplicative.ofAdd (Finsupp.single x 1)))
    (by
      intro r hr
      cases hr with
      | sign_sq =>
        rw [map_pow, FreeGroup.lift_apply_of]
        show (1 : ModTwoLamp X) ^ 2 = 1
        rw [one_pow]
      | lamp_sq x =>
        rw [map_pow, FreeGroup.lift_apply_of]
        have h2 : Finsupp.single x (1 : ZMod 2) +
            Finsupp.single x (1 : ZMod 2) = 0 := by
          rw [← Finsupp.single_add]
          have hzz : (1 : ZMod 2) + 1 = 0 := by decide
          rw [hzz, Finsupp.single_zero]
        show (Multiplicative.ofAdd (Finsupp.single x (1 : ZMod 2))) ^ 2 = 1
        rw [pow_two]
        show Multiplicative.ofAdd (Finsupp.single x (1 : ZMod 2) +
            Finsupp.single x (1 : ZMod 2)) = 1
        rw [h2]
        rfl
      | sign_comm x =>
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
      | @braiding x y _ =>
        rw [map_mul, map_inv, map_commutatorElement,
          FreeGroup.lift_apply_of, FreeGroup.lift_apply_of,
          FreeGroup.lift_apply_of]
        have hcomm : ⁅(Multiplicative.ofAdd
              (Finsupp.single x (1 : ZMod 2)) : ModTwoLamp X),
            Multiplicative.ofAdd (Finsupp.single y (1 : ZMod 2))⁆ = 1 :=
          commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
        show ⁅(Multiplicative.ofAdd
            (Finsupp.single x (1 : ZMod 2)) : ModTwoLamp X),
          Multiplicative.ofAdd (Finsupp.single y (1 : ZMod 2))⁆ *
            (1 : ModTwoLamp X)⁻¹ = 1
        rw [hcomm, inv_one, mul_one])

@[simp] theorem toModTwo_sign : toModTwo (sign X) = 1 := by
  show toModTwo (PresentedGroup.of (Sum.inl ())) = 1
  rfl

@[simp] theorem toModTwo_lamp (x : X) :
    toModTwo (lamp X x) =
      Multiplicative.ofAdd (Finsupp.single x (1 : ZMod 2)) := by
  show toModTwo (PresentedGroup.of (Sum.inr x)) =
    Multiplicative.ofAdd (Finsupp.single x (1 : ZMod 2))
  exact PresentedGroup.toGroup.of _

/-- Two homomorphisms out of the Clifford lamp group agreeing on the sign
and on every lamp are equal. -/
theorem cliffordHom_ext {G' : Type*} [Group G']
    {f g : CliffordLamp X →* G'}
    (hs : f (sign X) = g (sign X))
    (hl : ∀ x : X, f (lamp X x) = g (lamp X x)) : f = g := by
  apply MonoidHom.ext
  intro w
  have hmem : w ∈ f.eqLocus g := by
    apply mem_subgroup_of_sign_mem_of_lamp_mem X (f.eqLocus g)
    · exact hs
    · exact hl
  exact hmem

/-- The lamps are onto the mod-two model. -/
theorem toModTwo_surjective :
    Function.Surjective (toModTwo (X := X)) := by
  intro y
  have hy : y ∈ (toModTwo (X := X)).range := by
    have := mem_subgroup_of_single_mem (toModTwo (X := X)).range
      (fun x ↦ ⟨lamp X x, toModTwo_lamp x⟩) (Multiplicative.toAdd y)
    exact this
  exact hy

/-- The sign-free lamp quotient. -/
abbrev SignQuot (X : Type w) : Type w :=
  CliffordLamp X ⧸ Subgroup.zpowers (sign X)

instance signZpowersLamp_normal :
    (Subgroup.zpowers (sign X)).Normal := by
  constructor
  intro x hx g
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hc : sign X ^ n * g = g * sign X ^ n :=
    ((sign_commute X g).zpow_left n).eq
  have h1 : g * sign X ^ n * g⁻¹ = sign X ^ n := by
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [h1]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n

/-- The lamp class in the sign-free quotient. -/
def lampBar (x : X) : SignQuot X :=
  QuotientGroup.mk' (Subgroup.zpowers (sign X)) (lamp X x)

theorem lampBar_mul_self (x : X) : lampBar x * lampBar x = 1 := by
  show QuotientGroup.mk' (Subgroup.zpowers (sign X)) (lamp X x) *
      QuotientGroup.mk' (Subgroup.zpowers (sign X)) (lamp X x) = 1
  rw [← map_mul, ← pow_two, lamp_sq, map_one]

/-- Conjugation in the sign-free quotient fixes every lamp class: the
generators commute once the sign is dead. -/
theorem commute_mk_lamp (w : CliffordLamp X) (y : X) :
    Commute
      (QuotientGroup.mk' (Subgroup.zpowers (sign X)) (lamp X y))
      (QuotientGroup.mk' (Subgroup.zpowers (sign X)) w) := by
  have hhom : ((MulAut.conj (QuotientGroup.mk'
        (Subgroup.zpowers (sign X)) (lamp X y))).toMonoidHom.comp
        (QuotientGroup.mk' (Subgroup.zpowers (sign X)))) =
      QuotientGroup.mk' (Subgroup.zpowers (sign X)) := by
    apply cliffordHom_ext
    · show MulAut.conj _ (QuotientGroup.mk' _ (sign X)) = _
      have h1 : QuotientGroup.mk' (Subgroup.zpowers (sign X)) (sign X) =
          1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
      rw [h1, map_one]
    · intro x
      show MulAut.conj _ (QuotientGroup.mk' _ (lamp X x)) = _
      have hcomm : Commute
          (QuotientGroup.mk' (Subgroup.zpowers (sign X)) (lamp X y))
          (QuotientGroup.mk' (Subgroup.zpowers (sign X)) (lamp X x)) := by
        rcases eq_or_ne y x with rfl | hne
        · exact Commute.refl _
        · refine commutatorElement_eq_one_iff_commute.mp ?_
          rw [← map_commutatorElement,
            commutator_lamp_lamp X hne]
          exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
      show QuotientGroup.mk' (Subgroup.zpowers (sign X)) (lamp X y) *
          QuotientGroup.mk' (Subgroup.zpowers (sign X)) (lamp X x) *
          (QuotientGroup.mk' (Subgroup.zpowers (sign X)) (lamp X y))⁻¹ = _
      rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have := DFunLike.congr_fun hhom w
  show _ = _
  have hconj : QuotientGroup.mk' (Subgroup.zpowers (sign X)) (lamp X y) *
      QuotientGroup.mk' (Subgroup.zpowers (sign X)) w *
      (QuotientGroup.mk' (Subgroup.zpowers (sign X)) (lamp X y))⁻¹ =
      QuotientGroup.mk' (Subgroup.zpowers (sign X)) w := this
  exact mul_inv_eq_iff_eq_mul.mp hconj

/-- The sign-free lamp quotient is abelian. -/
instance : CommGroup (SignQuot X) :=
  { (inferInstance : Group (SignQuot X)) with
    mul_comm := by
      have hgen : ∀ w u : CliffordLamp X,
          Commute (QuotientGroup.mk' (Subgroup.zpowers (sign X)) w)
            (QuotientGroup.mk' (Subgroup.zpowers (sign X)) u) := by
        intro w u
        have hhom : ((MulAut.conj (QuotientGroup.mk'
              (Subgroup.zpowers (sign X)) w)).toMonoidHom.comp
              (QuotientGroup.mk' (Subgroup.zpowers (sign X)))) =
            QuotientGroup.mk' (Subgroup.zpowers (sign X)) := by
          apply cliffordHom_ext
          · show MulAut.conj _ (QuotientGroup.mk' _ (sign X)) = _
            have h1 : QuotientGroup.mk' (Subgroup.zpowers (sign X))
                (sign X) = 1 :=
              (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
            rw [h1, map_one]
          · intro x
            show MulAut.conj _ (QuotientGroup.mk' _ (lamp X x)) = _
            have hc := (commute_mk_lamp w x).symm
            show QuotientGroup.mk' (Subgroup.zpowers (sign X)) w *
                QuotientGroup.mk' (Subgroup.zpowers (sign X)) (lamp X x) *
                (QuotientGroup.mk' (Subgroup.zpowers (sign X)) w)⁻¹ = _
            rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
        have := DFunLike.congr_fun hhom u
        have hconj : QuotientGroup.mk' (Subgroup.zpowers (sign X)) w *
            QuotientGroup.mk' (Subgroup.zpowers (sign X)) u *
            (QuotientGroup.mk' (Subgroup.zpowers (sign X)) w)⁻¹ =
            QuotientGroup.mk' (Subgroup.zpowers (sign X)) u := this
        exact mul_inv_eq_iff_eq_mul.mp hconj
      intro a b
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective
        (Subgroup.zpowers (sign X)) a
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
        (Subgroup.zpowers (sign X)) b
      exact (hgen w u).eq }

/-- The point evaluation of the section: a mod-two coefficient becomes the
corresponding power of the lamp class. -/
def pointHom (x : X) : ZMod 2 →+ Additive (SignQuot X) where
  toFun b := ZMod.val b • Additive.ofMul (lampBar x)
  map_zero' := by
    rw [ZMod.val_zero, zero_smul]
  map_add' a b := by
    have h2 : (2 : ℕ) • Additive.ofMul (lampBar x) = 0 := by
      show Additive.ofMul (lampBar x) + Additive.ofMul (lampBar x) = 0
      show Additive.ofMul (lampBar x * lampBar x) = 0
      rw [lampBar_mul_self]
      rfl
    have hmod : ∀ m : ℕ,
        (m % 2) • Additive.ofMul (lampBar x) =
          m • Additive.ofMul (lampBar x) := by
      intro m
      conv_rhs => rw [← Nat.mod_add_div m 2]
      rw [add_nsmul, mul_nsmul, h2, smul_zero, add_zero]
    rw [ZMod.val_add, hmod, add_nsmul]

/-- The additive section of the abelianization. -/
noncomputable def psiAdd : (X →₀ ZMod 2) →+ Additive (SignQuot X) :=
  Finsupp.liftAddHom fun x ↦ pointHom x

/-- The multiplicative section of the abelianization. -/
noncomputable def psiHom : ModTwoLamp X →* SignQuot X :=
  MonoidHom.mk'
    (fun f ↦ Additive.toMul (psiAdd (Multiplicative.toAdd f)))
    (fun a b ↦ by
      show Additive.toMul
          (psiAdd (Multiplicative.toAdd a + Multiplicative.toAdd b)) = _
      rw [map_add]
      rfl)

theorem psiHom_single (x : X) :
    psiHom (Multiplicative.ofAdd (Finsupp.single x (1 : ZMod 2))) =
      lampBar x := by
  show Additive.toMul (psiAdd (Finsupp.single x (1 : ZMod 2))) = lampBar x
  have hlift : psiAdd (Finsupp.single x (1 : ZMod 2)) =
      pointHom x 1 := by
    show Finsupp.liftAddHom (fun x ↦ pointHom x)
      (Finsupp.single x (1 : ZMod 2)) = pointHom x 1
    rw [Finsupp.liftAddHom_apply_single]
  rw [hlift]
  show Additive.toMul
      (ZMod.val (1 : ZMod 2) • Additive.ofMul (lampBar x)) = lampBar x
  have hval : ZMod.val (1 : ZMod 2) = 1 := by decide
  rw [hval, one_smul]
  rfl

/-- The section splits the abelianization over the sign-free quotient. -/
theorem psiHom_comp_toModTwo :
    psiHom.comp (toModTwo (X := X)) =
      QuotientGroup.mk' (Subgroup.zpowers (sign X)) := by
  apply cliffordHom_ext
  · show psiHom (toModTwo (sign X)) = _
    rw [toModTwo_sign, map_one]
    have hmem : sign X ∈ Subgroup.zpowers (sign X) :=
      Subgroup.mem_zpowers _
    exact ((QuotientGroup.eq_one_iff _).mpr hmem).symm
  · intro x
    show psiHom (toModTwo (lamp X x)) = _
    rw [toModTwo_lamp, psiHom_single]
    rfl

/-- **The kernel of the abelianization is exactly the sign.** -/
theorem ker_toModTwo :
    (toModTwo (X := X)).ker = Subgroup.zpowers (sign X) := by
  apply le_antisymm
  · intro w hw
    have hmk : QuotientGroup.mk' (Subgroup.zpowers (sign X)) w = 1 := by
      have hpt := DFunLike.congr_fun
        (psiHom_comp_toModTwo (X := X)).symm w
      rw [hpt]
      show psiHom (toModTwo w) = 1
      rw [MonoidHom.mem_ker.mp hw, map_one]
    exact (QuotientGroup.eq_one_iff _).mp hmk
  · intro w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [MonoidHom.mem_ker, map_zpow, toModTwo_sign, one_zpow]

/-! ## The sign-free quotient of the ambient group -/

section Ambient

variable {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- The vertical action on mod-two lamps over the coset sites. -/
noncomputable def actF : Vertical α hα →* MulAut (ModTwoLamp (Cosets α hα)) :=
  finsuppActionHom
    (MulAction.toPermHom (Vertical α hα) (Cosets α hα))

/-- The abelianization intertwines the lamp actions. -/
theorem toModTwo_equivariant (v : Vertical α hα) :
    (toModTwo (X := Cosets α hα)).comp
        (lampAction α hα v).toMonoidHom =
      (actF α hα v).toMonoidHom.comp
        (toModTwo (X := Cosets α hα)) := by
  apply cliffordHom_ext
  · show toModTwo (lampAction α hα v (sign (Cosets α hα))) =
      actF α hα v (toModTwo (sign (Cosets α hα)))
    simp only [lampAction_apply_sign, toModTwo_sign, map_one]
  · intro x
    show toModTwo (lampAction α hα v (lamp (Cosets α hα) x)) =
      actF α hα v (toModTwo (lamp (Cosets α hα) x))
    rw [lampAction_apply_lamp, toModTwo_lamp, toModTwo_lamp]
    show _ = finsuppActionHom
        (MulAction.toPermHom (Vertical α hα) (Cosets α hα)) v
        (Multiplicative.ofAdd (Finsupp.single x 1))
    rw [finsuppActionHom_apply_single]
    rfl

/-- The abelianization of the whole ambient group. -/
noncomputable def Phi : Ambient α hα →*
    (ModTwoLamp (Cosets α hα) ⋊[actF α hα] Vertical α hα) :=
  SemidirectProduct.lift
    ((inl : ModTwoLamp (Cosets α hα) →*
        ModTwoLamp (Cosets α hα) ⋊[actF α hα] Vertical α hα).comp
      (toModTwo (X := Cosets α hα)))
    (inr : Vertical α hα →*
      ModTwoLamp (Cosets α hα) ⋊[actF α hα] Vertical α hα)
    (by
      intro v
      apply cliffordHom_ext
      · show inl (toModTwo (lampAction α hα v (sign (Cosets α hα)))) =
          MulAut.conj (inr v) (inl (toModTwo (sign (Cosets α hα))))
        simp only [lampAction_apply_sign, toModTwo_sign, map_one]
      · intro x
        show inl (toModTwo (lampAction α hα v (lamp (Cosets α hα) x))) =
          MulAut.conj (inr v) (inl (toModTwo (lamp (Cosets α hα) x)))
        have hconj : MulAut.conj (inr v)
            (inl (toModTwo (lamp (Cosets α hα) x)) :
              ModTwoLamp (Cosets α hα) ⋊[actF α hα] Vertical α hα) =
            inl (actF α hα v (toModTwo (lamp (Cosets α hα) x))) := by
          show (inr v : ModTwoLamp (Cosets α hα) ⋊[actF α hα]
              Vertical α hα) * inl (toModTwo (lamp (Cosets α hα) x)) *
              (inr v)⁻¹ = _
          rw [inl_aut, map_inv]
        rw [hconj]
        have := DFunLike.congr_fun (toModTwo_equivariant α hα v)
          (lamp (Cosets α hα) x)
        exact congrArg inl this)

theorem Phi_apply (p : Ambient α hα) :
    Phi α hα p = ⟨toModTwo p.left, p.right⟩ := by
  have hp : p = inl p.left * inr p.right :=
    (inl_left_mul_inr_right p).symm
  conv_lhs => rw [hp]
  rw [map_mul]
  have h1 : Phi α hα (inl p.left) = inl (toModTwo p.left) := by
    show SemidirectProduct.lift _ _ _ (inl p.left) = _
    rw [SemidirectProduct.lift_inl]
    rfl
  have h2 : Phi α hα (inr p.right) = inr p.right := by
    show SemidirectProduct.lift _ _ _ (inr p.right) = _
    rw [SemidirectProduct.lift_inr]
  rw [h1, h2]
  exact inl_left_mul_inr_right
    (⟨toModTwo p.left, p.right⟩ :
      ModTwoLamp (Cosets α hα) ⋊[actF α hα] Vertical α hα)

theorem Phi_surjective : Function.Surjective (Phi α hα) := by
  intro q
  obtain ⟨n, hn⟩ := toModTwo_surjective (X := Cosets α hα) q.left
  refine ⟨⟨n, q.right⟩, ?_⟩
  rw [Phi_apply]
  apply SemidirectProduct.ext
  · exact hn
  · rfl

theorem ker_Phi :
    (Phi α hα).ker = Subgroup.zpowers (signAmbient α hα) := by
  ext p
  rw [MonoidHom.mem_ker, Phi_apply]
  constructor
  · intro h1
    have hleft : toModTwo p.left = 1 := congrArg SemidirectProduct.left h1
    have hright : p.right = 1 := congrArg SemidirectProduct.right h1
    have hker : p.left ∈ (toModTwo (X := Cosets α hα)).ker :=
      MonoidHom.mem_ker.mpr hleft
    rw [ker_toModTwo] at hker
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hker
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    have hsign : (signAmbient α hα) ^ n =
        (inl (sign (Cosets α hα) ^ n) : Ambient α hα) := by
      show (inl (sign (Cosets α hα)) : Ambient α hα) ^ n = _
      rw [← map_zpow]
    rw [hsign, hn]
    apply SemidirectProduct.ext
    · rfl
    · exact hright.symm
  · intro hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hsign : (signAmbient α hα) ^ n =
        (inl (sign (Cosets α hα) ^ n) : Ambient α hα) := by
      show (inl (sign (Cosets α hα)) : Ambient α hα) ^ n = _
      rw [← map_zpow]
    rw [← hn, hsign]
    apply SemidirectProduct.ext
    · show toModTwo (sign (Cosets α hα) ^ n) = 1
      rw [map_zpow, toModTwo_sign, one_zpow]
    · rfl

/-- **The sign-free quotient is the mod-two lamp group under the vertical
action.** -/
noncomputable def signFreeQuotientEquiv :
    (Ambient α hα ⧸ Subgroup.zpowers (signAmbient α hα)) ≃*
      (ModTwoLamp (Cosets α hα) ⋊[actF α hα] Vertical α hα) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_Phi α hα).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (Phi α hα)
      (Phi_surjective α hα))

/-! ## Soficity -/

/-- The mod-two-lamp-by-telescope subgroup is sofic. -/
theorem isSofic_modTwo_telescope [α.range.FiniteIndex] (hΓ : IsSofic Γ) :
    IsSofic
      (ModTwoLamp (Cosets α hα) ⋊[
        SemidirectAssoc.baseAction (shiftHom α hα) (actF α hα)]
        Telescope α hα) := by
  classical
  apply isSofic_semidirectProduct_of_invariant_finite
  intro F
  choose lvl elt hrepr using fun g :
    ModTwoLamp (Cosets α hα) ⋊[
      SemidirectAssoc.baseAction (shiftHom α hα) (actF α hα)]
      Telescope α hα ↦ exists_level_repr α hα g.right
  let N : ℕ := F.sup lvl
  let H : Subgroup (Telescope α hα) := (level α hα N).range
  obtain ⟨K, hKfinite, hKinvariant, hKcontains⟩ :=
    exists_finite_invariant_modTwo_subgroup
      (SoficMarkedCompression.levelSiteAction α hα N)
      (SoficMarkedCompression.finite_levelSiteAction_orbit α hα N)
      (F.image SemidirectProduct.left)
  refine ⟨K, H, hKfinite, isSofic_level_range α hα hΓ N, ?_, ?_⟩
  · intro h hh n hn
    exact hKinvariant (⟨h, hh⟩ : H) n hn
  · intro g hg
    constructor
    · exact hKcontains g.left (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    · have hle : lvl g ≤ N := Finset.le_sup (f := lvl) hg
      have hmem := level_mem_range_of_le α hα hle (elt g)
      rwa [hrepr g] at hmem

/-- The mod-two lamp model of the full witness is sofic. -/
theorem isSofic_signFreeModel [α.range.FiniteIndex] (hΓ : IsSofic Γ) :
    IsSofic (ModTwoLamp (Cosets α hα) ⋊[actF α hα] Vertical α hα) := by
  have hinner := isSofic_modTwo_telescope α hα hΓ
  have houter : IsSofic
      ((ModTwoLamp (Cosets α hα) ⋊[
          SemidirectAssoc.baseAction (shiftHom α hα) (actF α hα)]
          Telescope α hα) ⋊[
        SemidirectAssoc.outerAction (shiftHom α hα) (actF α hα)]
        Multiplicative ℤ) :=
    SoficIntegerExtension.isSofic_int_semidirectProduct
      (SemidirectAssoc.outerAction (shiftHom α hα) (actF α hα)) hinner
  exact (isSofic_mulEquiv_iff
    (SemidirectAssoc.assocEquiv (shiftHom α hα) (actF α hα))).mp houter

/-- **The sign-free quotient of the marked-compression witness is
sofic.** -/
theorem isSofic_signFreeQuotient [α.range.FiniteIndex] (hΓ : IsSofic Γ) :
    IsSofic (Ambient α hα ⧸ Subgroup.zpowers (signAmbient α hα)) :=
  (isSofic_mulEquiv_iff (signFreeQuotientEquiv α hα)).mpr
    (isSofic_signFreeModel α hα hΓ)

end Ambient

/-! ## The literal endpoints -/

section Literal

open LiteralNonMFLinearWitness ExplicitLinearModel

/- Quotients of countable groups are countable.  Proved once as
`GroupApproximation.CountableInstances.quotientCountable` and taken here with
the same `local` scope the mirrored copy had. -/
attribute [local instance] GroupApproximation.CountableInstances.quotientCountable

/-- **The literal commuting-lamp quotient is sofic.** -/
theorem literalSignFreeQuotient_isSofic :
    IsSofic (Ambient alpha conjD_injective ⧸
      Subgroup.zpowers (signAmbient alpha conjD_injective)) :=
  isSofic_signFreeQuotient alpha conjD_injective
    ExplicitIntegralLinearModel.gammaBar_isSofic

/-- **An explicit sofic group that is not MF.**  The commuting-lamp
quotient of the witness group is sofic, and it admits no injective
corona representation. -/
theorem literalSignFreeQuotient_isSofic_and_not_isCDEOperatorMF :
    IsSofic (Ambient alpha conjD_injective ⧸
        Subgroup.zpowers (signAmbient alpha conjD_injective)) ∧
      ¬ IsCDEOperatorMF (Ambient alpha conjD_injective ⧸
        Subgroup.zpowers (signAmbient alpha conjD_injective)) :=
  ⟨literalSignFreeQuotient_isSofic,
    CommutingLampCollapse.literalCommutingLampQuotient_not_isCDEOperatorMF⟩

end Literal

end CommutingLampQuotientSofic
end GroupApproximation
