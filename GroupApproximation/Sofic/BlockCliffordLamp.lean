import GroupApproximation.Sofic.CliffordLampGroup
import GroupApproximation.Sofic.FreeProductSignReflection

/-!
# The block Clifford lamp group is residually finite

The block Clifford lamp group on a family of blocks is presented like the
Clifford lamp group, except that only *same-block* pairs of lamps
anticommute through the central sign; lamps in different blocks satisfy
no relation.  This is the abstract avatar of the literal lamp
sub-amalgams `M_J`: the free product of copies of `ClLamp(8)`
amalgamated over the common central sign, for the disjoint-clique
orbital graph.

Residual finiteness is the two-quotient argument of
`notes/SOFICITY_TOWER_MJ_DESIGN_2026-08-15.md` §3(C), instantiated:

* the sign is central of order two, so the kernel of killing it is
  exactly its two-element cyclic subgroup;
* the quotient by the sign is the plain free product of the block sign
  groups — residually finite by
  `FreeProductSignReflection.residuallyFinite_coprodI_signGroup`;
* the sign survives the finite signed model of the *complete* Clifford
  lamp group on all sites, along the homomorphism that imposes the
  missing cross-block anticommutation relations;
* `residuallyFinite_of_central_involution_detected` closes.

The quotient identification does not compute a normal form: the free
product receives a section built from commuting involutions, and a
left inverse on generators is all that injectivity needs.
-/

namespace GroupApproximation
namespace BlockCliffordLamp

open Monoid Finset FreeProductSignReflection
open scoped symmDiff commutatorElement

set_option linter.unusedSectionVars true

variable (I : Type) [DecidableEq I] [Fintype I]
variable (B : I → Type) [∀ i, DecidableEq (B i)] [∀ i, Fintype (B i)]

/-! ## Commuting-involution products

A family of pairwise commuting involutions in any group receives a
homomorphism from the corresponding sign group, sending a sign vector to
the product of the involutions in its support. -/

section SignProd

variable {G : Type*} [Group G] {β : Type} [Fintype β] [DecidableEq β]
variable (t : β → G) (hcomm : ∀ a b, Commute (t a) (t b))

/-- The support of a sign vector, as a finset. -/
def sset (ε : β → Multiplicative (ZMod 2)) : Finset β :=
  Finset.univ.filter fun b => Multiplicative.toAdd (ε b) = 1

omit [DecidableEq β] in
theorem sset_one : sset (1 : β → Multiplicative (ZMod 2)) = ∅ := by
  rw [sset, Finset.filter_eq_empty_iff]
  intro b _
  simp only [Pi.one_apply, toAdd_one]
  decide

theorem sset_mul (ε ε' : β → Multiplicative (ZMod 2)) :
    sset (ε * ε') = sset ε ∆ sset ε' := by
  have hxor : ∀ a b : ZMod 2, a + b = 1 ↔
      ((a = 1 ∧ ¬b = 1) ∨ (¬a = 1 ∧ b = 1)) := by decide
  ext b
  simp only [sset, Finset.mem_symmDiff, mem_filter, mem_univ, true_and]
  have : Multiplicative.toAdd ((ε * ε') b)
      = Multiplicative.toAdd (ε b) + Multiplicative.toAdd (ε' b) := rfl
  rw [this, hxor]
  tauto

/-- The product of the involutions over a finset. -/
def prodOf (s : Finset β) : G :=
  s.noncommProd t fun a _ b _ _ => hcomm a b

omit [Fintype β] [DecidableEq β] in
theorem prodOf_empty : prodOf t hcomm (∅ : Finset β) = 1 :=
  Finset.noncommProd_empty _ _

omit [Fintype β] [DecidableEq β] in
theorem prodOf_singleton (b : β) : prodOf t hcomm {b} = t b :=
  Finset.noncommProd_singleton _ _

omit [Fintype β] in
theorem prodOf_union {s u : Finset β} (h : Disjoint s u) :
    prodOf t hcomm (s ∪ u) = prodOf t hcomm s * prodOf t hcomm u :=
  Finset.noncommProd_union_of_disjoint h _ _

omit [Fintype β] [DecidableEq β] in
theorem commute_prodOf (g : G) (hg : ∀ b, Commute g (t b))
    (s : Finset β) : Commute g (prodOf t hcomm s) :=
  Finset.noncommProd_commute _ _ _ _ fun b _ => hg b

omit [Fintype β] [DecidableEq β] in
theorem prodOf_commute (s u : Finset β) :
    Commute (prodOf t hcomm s) (prodOf t hcomm u) := by
  apply commute_prodOf
  intro b
  exact (commute_prodOf t hcomm (t b) (fun a => hcomm b a) s).symm

omit [Fintype β] in
theorem prodOf_sq (hsq : ∀ b, t b * t b = 1) (s : Finset β) :
    prodOf t hcomm s * prodOf t hcomm s = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [prodOf_empty, one_mul]
  | insert a s ha ih =>
      rw [prodOf, Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
      have hP : Commute (t a)
          (prodOf t hcomm s) :=
        commute_prodOf t hcomm (t a) (fun b => hcomm a b) s
      show t a * prodOf t hcomm s * (t a * prodOf t hcomm s) = 1
      calc t a * prodOf t hcomm s * (t a * prodOf t hcomm s)
          = t a * (prodOf t hcomm s * t a) * prodOf t hcomm s := by
            group
        _ = t a * (t a * prodOf t hcomm s) * prodOf t hcomm s := by
            rw [hP.symm.eq]
        _ = (t a * t a) * (prodOf t hcomm s * prodOf t hcomm s) := by
            group
        _ = 1 := by rw [hsq a, ih, one_mul]

omit [Fintype β] in
theorem prodOf_symmDiff (hsq : ∀ b, t b * t b = 1) (s u : Finset β) :
    prodOf t hcomm (s ∆ u) = prodOf t hcomm s * prodOf t hcomm u := by
  classical
  have hd1 : Disjoint (s \ u) (s ∩ u) := Finset.disjoint_sdiff_inter s u
  have hd2 : Disjoint (u \ s) (u ∩ s) := Finset.disjoint_sdiff_inter u s
  have hd3 : Disjoint (s \ u) (u \ s) := disjoint_sdiff_sdiff
  have hs : prodOf t hcomm s
      = prodOf t hcomm (s \ u) * prodOf t hcomm (s ∩ u) := by
    rw [← prodOf_union t hcomm hd1, Finset.sdiff_union_inter]
  have hu : prodOf t hcomm u
      = prodOf t hcomm (u \ s) * prodOf t hcomm (s ∩ u) := by
    rw [Finset.inter_comm s u, ← prodOf_union t hcomm hd2,
      Finset.sdiff_union_inter]
  have hunion : s ∆ u = (s \ u) ∪ (u \ s) := by
    rw [Finset.symmDiff_def]
  have hsd : prodOf t hcomm (s ∆ u)
      = prodOf t hcomm (s \ u) * prodOf t hcomm (u \ s) := by
    rw [hunion, prodOf_union t hcomm hd3]
  rw [hsd, hs, hu]
  have hDC : Commute (prodOf t hcomm (s ∩ u)) (prodOf t hcomm (u \ s)) :=
    prodOf_commute t hcomm _ _
  have hsq' := prodOf_sq t hcomm hsq (s ∩ u)
  calc prodOf t hcomm (s \ u) * prodOf t hcomm (u \ s)
      = prodOf t hcomm (s \ u) * prodOf t hcomm (u \ s) *
          (prodOf t hcomm (s ∩ u) * prodOf t hcomm (s ∩ u)) := by
        rw [hsq', mul_one]
    _ = prodOf t hcomm (s \ u) *
          (prodOf t hcomm (u \ s) * prodOf t hcomm (s ∩ u)) *
          prodOf t hcomm (s ∩ u) := by group
    _ = prodOf t hcomm (s \ u) *
          (prodOf t hcomm (s ∩ u) * prodOf t hcomm (u \ s)) *
          prodOf t hcomm (s ∩ u) := by rw [hDC.eq]
    _ = prodOf t hcomm (s \ u) * prodOf t hcomm (s ∩ u) *
          (prodOf t hcomm (u \ s) * prodOf t hcomm (s ∩ u)) := by group

/-- The homomorphism from the sign group determined by a family of
pairwise commuting involutions. -/
def signProdHom (hsq : ∀ b, t b * t b = 1) :
    (β → Multiplicative (ZMod 2)) →* G where
  toFun ε := prodOf t hcomm (sset ε)
  map_one' := by rw [sset_one, prodOf_empty]
  map_mul' ε ε' := by
    rw [sset_mul, prodOf_symmDiff t hcomm hsq]

@[simp]
theorem signProdHom_apply (hsq : ∀ b, t b * t b = 1)
    (ε : β → Multiplicative (ZMod 2)) :
    signProdHom t hcomm hsq ε = prodOf t hcomm (sset ε) := rfl

end SignProd

/-! ## The presentation -/

/-- Free generators: the sign and one lamp per site. -/
abbrev Gen := (Unit ⊕ ((i : I) × B i))

/-- The block Clifford relator families: the sign and the lamps are
involutions, the sign is central, and two distinct lamps *in the same
block* anticommute through the sign.  Lamps in different blocks satisfy
no relation. -/
inductive IsRelator : FreeGroup (Gen I B) → Prop
  | sign_sq : IsRelator (FreeGroup.of (Sum.inl ()) ^ 2)
  | lamp_sq (p : (i : I) × B i) : IsRelator (FreeGroup.of (Sum.inr p) ^ 2)
  | sign_comm (p : (i : I) × B i) :
      IsRelator ⁅(FreeGroup.of (Sum.inl ()) : FreeGroup (Gen I B)),
        FreeGroup.of (Sum.inr p)⁆
  | braiding {i : I} {b b' : B i} (h : b ≠ b') :
      IsRelator (⁅(FreeGroup.of (Sum.inr ⟨i, b⟩) : FreeGroup (Gen I B)),
          FreeGroup.of (Sum.inr ⟨i, b'⟩)⁆ *
        (FreeGroup.of (Sum.inl ()))⁻¹)

/-- The block Clifford relators as a set. -/
def relators : Set (FreeGroup (Gen I B)) := {w | IsRelator I B w}

/-- The presented block Clifford lamp group. -/
abbrev BlockClifford := PresentedGroup (relators I B)

/-- The central sign. -/
def sign : BlockClifford I B := PresentedGroup.of (Sum.inl ())

/-- The lamp at a site. -/
def lamp (p : (i : I) × B i) : BlockClifford I B :=
  PresentedGroup.of (Sum.inr p)

omit [DecidableEq I] [Fintype I] [∀ i, DecidableEq (B i)] [∀ i, Fintype (B i)] in
theorem sign_sq : sign I B ^ 2 = 1 := by
  have := PresentedGroup.one_of_mem (IsRelator.sign_sq (I := I) (B := B))
  rwa [map_pow] at this

omit [DecidableEq I] [Fintype I] [∀ i, DecidableEq (B i)] [∀ i, Fintype (B i)] in
theorem lamp_sq (p : (i : I) × B i) : lamp I B p ^ 2 = 1 := by
  have := PresentedGroup.one_of_mem (IsRelator.lamp_sq (I := I) (B := B) p)
  rwa [map_pow] at this

omit [DecidableEq I] [Fintype I] [∀ i, DecidableEq (B i)] [∀ i, Fintype (B i)] in
theorem sign_commute_lamp (p : (i : I) × B i) :
    Commute (sign I B) (lamp I B p) := by
  have := PresentedGroup.one_of_mem
    (IsRelator.sign_comm (I := I) (B := B) p)
  rw [map_commutatorElement] at this
  exact commutatorElement_eq_one_iff_commute.mp this

omit [DecidableEq I] [Fintype I] [∀ i, DecidableEq (B i)] [∀ i, Fintype (B i)] in
theorem commutator_lamp_lamp {i : I} {b b' : B i} (h : b ≠ b') :
    ⁅lamp I B ⟨i, b⟩, lamp I B ⟨i, b'⟩⁆ = sign I B := by
  have h1 := PresentedGroup.one_of_mem
    (IsRelator.braiding (I := I) (B := B) h)
  rw [map_mul, map_inv, map_commutatorElement] at h1
  have h2 : ⁅lamp I B ⟨i, b⟩, lamp I B ⟨i, b'⟩⁆ * (sign I B)⁻¹ = 1 := h1
  calc ⁅lamp I B ⟨i, b⟩, lamp I B ⟨i, b'⟩⁆
      = ⁅lamp I B ⟨i, b⟩, lamp I B ⟨i, b'⟩⁆ * (sign I B)⁻¹ * sign I B := by
        group
    _ = 1 * sign I B := by rw [h2]
    _ = sign I B := one_mul _

omit [DecidableEq I] [Fintype I] [∀ i, DecidableEq (B i)] [∀ i, Fintype (B i)] in
/-- The sign is central. -/
theorem sign_commute (g : BlockClifford I B) :
    Commute (sign I B) g := by
  have hmem : g ∈ Subgroup.centralizer {sign I B} := by
    apply PresentedGroup.generated_by (relators I B)
      (Subgroup.centralizer {sign I B}) (fun j => ?_) g
    rw [Subgroup.mem_centralizer_singleton_iff]
    match j with
    | Sum.inl () => rfl
    | Sum.inr p => exact (sign_commute_lamp I B p).eq.symm
  rw [Subgroup.mem_centralizer_singleton_iff] at hmem
  exact Commute.symm hmem

omit [DecidableEq I] [Fintype I] [∀ i, DecidableEq (B i)] [∀ i, Fintype (B i)] in
theorem sign_mem_center : sign I B ∈ Subgroup.center (BlockClifford I B) :=
  Subgroup.mem_center_iff.mpr fun g => ((sign_commute I B g).symm).eq

/-! ## The detector: the complete Clifford lamp group on all sites -/

/-- Generator images in the complete Clifford lamp group: impose the
missing cross-block anticommutation relations. -/
def fullGenerator : Gen I B → CliffordLamp.CliffordLamp ((i : I) × B i) :=
  Sum.elim (fun _ => CliffordLamp.sign _) fun p => CliffordLamp.lamp _ p

omit [DecidableEq I] [Fintype I] [∀ i, DecidableEq (B i)] [∀ i, Fintype (B i)] in
theorem fullGenerator_kills :
    ∀ w ∈ relators I B,
      FreeGroup.lift (fullGenerator I B) w = 1 := by
  intro w hw
  change IsRelator I B w at hw
  cases hw with
  | sign_sq =>
      rw [map_pow, FreeGroup.lift_apply_of]
      exact CliffordLamp.sign_sq _
  | lamp_sq p =>
      rw [map_pow, FreeGroup.lift_apply_of]
      exact CliffordLamp.lamp_sq _ p
  | sign_comm p =>
      rw [map_commutatorElement, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of]
      exact (CliffordLamp.sign_commute_lamp _ p).commutator_eq
  | @braiding i b b' h =>
      rw [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      show ⁅CliffordLamp.lamp ((i : I) × B i) ⟨i, b⟩,
          CliffordLamp.lamp ((i : I) × B i) ⟨i, b'⟩⁆ *
          (CliffordLamp.sign ((i : I) × B i))⁻¹ = 1
      rw [CliffordLamp.commutator_lamp_lamp ((i : I) × B i)
        (fun hc => h (sigma_mk_injective hc))]
      exact mul_inv_cancel _

/-- The homomorphism to the complete Clifford lamp group. -/
def toFull : BlockClifford I B →*
    CliffordLamp.CliffordLamp ((i : I) × B i) :=
  PresentedGroup.toGroup (fullGenerator_kills I B)

omit [DecidableEq I] [Fintype I] [(i : I) → DecidableEq (B i)] [(i : I) → Fintype (B i)] in
@[simp] theorem toFull_sign :
    toFull I B (sign I B) = CliffordLamp.sign _ :=
  PresentedGroup.toGroup.of _

/-! ## The free-product quotient -/

/-- One coordinate flip in the sign group of block `i`. -/
def coordFlip (i : I) (b : B i) : SignGroup B i :=
  fun b' => if b' = b then Multiplicative.ofAdd 1 else 1

omit [DecidableEq I] [Fintype I] [∀ i, Fintype (B i)] in
theorem coordFlip_mul_self (i : I) (b : B i) :
    coordFlip I B i b * coordFlip I B i b = 1 := by
  funext b'
  by_cases hb : b' = b <;>
    simp only [coordFlip, Pi.mul_apply, Pi.one_apply, hb, if_true, if_false] <;>
    decide

omit [DecidableEq I] [Fintype I] in
theorem sset_coordFlip (i : I) (b : B i) :
    sset (β := B i) (coordFlip I B i b) = {b} := by
  ext b'
  rw [Finset.mem_singleton]
  constructor
  · intro h
    rw [sset, mem_filter] at h
    by_contra hb
    have h2 := h.2
    rw [show coordFlip I B i b b' = 1 from if_neg hb] at h2
    exact absurd h2 (by decide)
  · intro h
    subst h
    rw [sset, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [show coordFlip I B i b' b' = Multiplicative.ofAdd 1 from if_pos rfl]
    decide

/-- Generator images in the free product: the sign dies, the lamp at
`(i, b)` becomes the coordinate flip. -/
def freeGenerator : Gen I B → Monoid.CoprodI (SignGroup B) :=
  Sum.elim (fun _ => 1) fun p => Monoid.CoprodI.of (coordFlip I B p.1 p.2)

omit [DecidableEq I] [Fintype I] [(i : I) → Fintype (B i)] in
theorem freeGenerator_kills :
    ∀ w ∈ relators I B,
      FreeGroup.lift (freeGenerator I B) w = 1 := by
  intro w hw
  change IsRelator I B w at hw
  cases hw with
  | sign_sq =>
      rw [map_pow, FreeGroup.lift_apply_of]
      show (1 : Monoid.CoprodI (SignGroup B)) ^ 2 = 1
      rw [one_pow]
  | lamp_sq p =>
      rw [map_pow, FreeGroup.lift_apply_of]
      show Monoid.CoprodI.of (coordFlip I B p.1 p.2) ^ 2 = 1
      rw [pow_two, ← map_mul, coordFlip_mul_self, map_one]
  | sign_comm p =>
      rw [map_commutatorElement, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of]
      show ⁅(1 : Monoid.CoprodI (SignGroup B)), _⁆ = 1
      rw [commutatorElement_eq_one_iff_commute]
      exact Commute.one_left _
  | @braiding i b b' h =>
      rw [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      show ⁅Monoid.CoprodI.of (coordFlip I B i b), Monoid.CoprodI.of (coordFlip I B i b')⁆ *
          ((1 : Monoid.CoprodI (SignGroup B)))⁻¹ = 1
      rw [commutatorElement_def, ← map_mul, ← map_inv, ← map_inv, ← map_mul,
        ← map_mul]
      have hc : coordFlip I B i b * coordFlip I B i b' * (coordFlip I B i b)⁻¹ *
          (coordFlip I B i b')⁻¹ = 1 := by
        have : coordFlip I B i b * coordFlip I B i b' = coordFlip I B i b' * coordFlip I B i b :=
          mul_comm _ _
        rw [this, mul_assoc, mul_assoc]
        rw [← mul_assoc (coordFlip I B i b) (coordFlip I B i b)⁻¹]
        simp
      rw [hc, map_one, inv_one, mul_one]

/-- The homomorphism onto the free product of the block sign groups. -/
def toFree : BlockClifford I B →* Monoid.CoprodI (SignGroup B) :=
  PresentedGroup.toGroup (freeGenerator_kills I B)

omit [DecidableEq I] [Fintype I] [(i : I) → Fintype (B i)] in
@[simp] theorem toFree_sign : toFree I B (sign I B) = 1 :=
  PresentedGroup.toGroup.of _

omit [DecidableEq I] [Fintype I] [(i : I) → Fintype (B i)] in
@[simp] theorem toFree_lamp (p : (i : I) × B i) :
    toFree I B (lamp I B p) = Monoid.CoprodI.of (coordFlip I B p.1 p.2) :=
  PresentedGroup.toGroup.of _

/-! ## The section and injectivity of the descended quotient map -/

/-- The sign subgroup. -/
abbrev signSubgroup : Subgroup (BlockClifford I B) :=
  Subgroup.zpowers (sign I B)

instance : (signSubgroup I B).Normal :=
  normal_zpowers_of_mem_center (sign_mem_center I B)

/-- The quotient by the sign. -/
abbrev BarBlock := BlockClifford I B ⧸ signSubgroup I B

/-- The lamp in the quotient. -/
def lampBar (p : (i : I) × B i) : BarBlock I B :=
  QuotientGroup.mk' _ (lamp I B p)

omit [DecidableEq I] [Fintype I] [(i : I) → DecidableEq (B i)] [(i : I) → Fintype (B i)] in
theorem lampBar_sq (p : (i : I) × B i) :
    lampBar I B p * lampBar I B p = 1 := by
  rw [lampBar, ← map_mul, ← pow_two, lamp_sq, map_one]

omit [DecidableEq I] [Fintype I] [(i : I) → Fintype (B i)] in
theorem lampBar_commute {i : I} (b b' : B i) :
    Commute (lampBar I B ⟨i, b⟩) (lampBar I B ⟨i, b'⟩) := by
  by_cases h : b = b'
  · subst h; exact Commute.refl _
  · have hone : ⁅lampBar I B ⟨i, b⟩, lampBar I B ⟨i, b'⟩⁆ = 1 := by
      rw [lampBar, lampBar, ← map_commutatorElement,
        commutator_lamp_lamp I B h, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact Subgroup.mem_zpowers _
    exact commutatorElement_eq_one_iff_commute.mp hone

/-- The section from the free product into the quotient, sending a sign
vector to the product of its lamps — a homomorphism because same-block
lamps commute once the sign dies. -/
def fromFree : Monoid.CoprodI (SignGroup B) →* BarBlock I B :=
  Monoid.CoprodI.lift fun i =>
    signProdHom (fun b => lampBar I B ⟨i, b⟩)
      (fun a b => lampBar_commute I B a b)
      (fun b => lampBar_sq I B ⟨i, b⟩)

omit [DecidableEq I] [Fintype I] in
theorem fromFree_of_coordFlip (i : I) (b : B i) :
    fromFree I B (Monoid.CoprodI.of (coordFlip I B i b)) = lampBar I B ⟨i, b⟩ := by
  rw [fromFree, Monoid.CoprodI.lift_of, signProdHom_apply, sset_coordFlip,
    prodOf_singleton]

/-- The quotient map to the free product, descended along the sign. -/
def toFreeBar : BarBlock I B →* Monoid.CoprodI (SignGroup B) :=
  QuotientGroup.lift _ (toFree I B) (by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [MonoidHom.mem_ker, map_zpow, toFree_sign, one_zpow])

omit [DecidableEq I] [Fintype I] [(i : I) → Fintype (B i)] in
@[simp] theorem toFreeBar_mk (g : BlockClifford I B) :
    toFreeBar I B (QuotientGroup.mk' _ g) = toFree I B g := rfl

omit [DecidableEq I] [Fintype I] in
/-- The section is a left inverse on the quotient. -/
theorem fromFree_comp_toFreeBar :
    (fromFree I B).comp (toFreeBar I B) = MonoidHom.id (BarBlock I B) := by
  apply QuotientGroup.monoidHom_ext
  apply PresentedGroup.ext
  intro x
  match x with
  | Sum.inl () =>
      show fromFree I B (toFree I B (sign I B))
        = QuotientGroup.mk' (signSubgroup I B) (sign I B)
      rw [toFree_sign, map_one, QuotientGroup.mk'_apply, eq_comm,
        QuotientGroup.eq_one_iff]
      exact Subgroup.mem_zpowers _
  | Sum.inr p =>
      show fromFree I B (toFree I B (lamp I B p))
        = QuotientGroup.mk' (signSubgroup I B) (lamp I B p)
      rw [toFree_lamp, fromFree_of_coordFlip]
      rfl

omit [DecidableEq I] [Fintype I] in
theorem toFreeBar_injective : Function.Injective (toFreeBar I B) := by
  intro x y hxy
  have hx := DFunLike.congr_fun (fromFree_comp_toFreeBar I B) x
  have hy := DFunLike.congr_fun (fromFree_comp_toFreeBar I B) y
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply]
    at hx hy
  rw [← hx, ← hy, hxy]

/-! ## The finite detector and the conclusion -/

/-- Any finite site type carries a linear order, which the signed model's
crossing cocycle needs. -/
noncomputable instance : LinearOrder ((i : I) × B i) :=
  LinearOrder.lift' (Fintype.equivFin ((i : I) × B i))
    (Equiv.injective _)

instance : Finite (CliffordLamp.SignedModel ((i : I) × B i)) := by
  apply Finite.of_injective
    (fun p : CliffordLamp.SignedModel ((i : I) × B i) =>
      ((p.signPart, fun x => p.config x) :
        ZMod 2 × (((i : I) × B i) → ZMod 2)))
  intro p q h
  ext : 1
  · exact congrArg Prod.fst h
  · exact Finsupp.ext fun x => congrFun (congrArg Prod.snd h) x

/-- The detector: impose the cross-block relations, then evaluate in the
finite signed model. -/
noncomputable def detector : BlockClifford I B →*
    CliffordLamp.SignedModel ((i : I) × B i) :=
  (CliffordLamp.toModel ((i : I) × B i)).comp (toFull I B)

omit [DecidableEq I] [(i : I) → DecidableEq (B i)] in
theorem detector_sign_ne_one : detector I B (sign I B) ≠ 1 := by
  rw [detector, MonoidHom.comp_apply, toFull_sign,
    CliffordLamp.toModel_sign]
  intro h
  have hpart := congrArg CliffordLamp.SignedModel.signPart h
  rw [CliffordLamp.one_def] at hpart
  have h10 : (1 : ZMod 2) = 0 := hpart
  exact absurd h10 (by decide)

/-- **The block Clifford lamp group is residually finite.**  The sign is a
detected central involution: its quotient is the plain free product of the
block sign groups — residually finite by the signed-reflection theorem —
and it survives the finite signed model of the complete Clifford lamp
group. -/
theorem residuallyFinite_blockClifford :
    Group.ResiduallyFinite (BlockClifford I B) := by
  haveI : Group.ResiduallyFinite
      (BlockClifford I B ⧸ Subgroup.zpowers (sign I B)) := by
    haveI := residuallyFinite_coprodI_signGroup (B := B)
    exact residuallyFinite_of_injective (toFreeBar I B)
      (toFreeBar_injective I B)
  exact residuallyFinite_of_central_involution_detected
    (z := sign I B) (sign_sq I B)
    (detector I B) (detector_sign_ne_one I B)


/-! ## Block-preserving permutations act on the block Clifford group -/

omit [DecidableEq I] [Fintype I] [∀ i, DecidableEq (B i)] [∀ i, Fintype (B i)] in
/-- The commutator of two distinct same-block lamps is the sign, in the
first-component form. -/
theorem commutator_lamp_lamp' {p q : (i : I) × B i}
    (hfst : p.1 = q.1) (hne : p ≠ q) :
    ⁅lamp I B p, lamp I B q⁆ = sign I B := by
  obtain ⟨i, b⟩ := p
  obtain ⟨j, b'⟩ := q
  obtain rfl : i = j := hfst
  have hb : b ≠ b' := by
    intro hc
    exact hne (by rw [hc])
  exact commutator_lamp_lamp I B hb

/-- The subgroup of site permutations that preserve the block structure:
two sites lie in the same block exactly when their images do. -/
def blockPermSubgroup : Subgroup (Equiv.Perm ((i : I) × B i)) where
  carrier := {π | ∀ p q : (i : I) × B i, (π p).1 = (π q).1 ↔ p.1 = q.1}
  one_mem' := by
    intro p q
    simp
  mul_mem' := by
    intro π τ hπ hτ p q
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hπ (τ p) (τ q), hτ p q]
  inv_mem' := by
    intro π hπ p q
    have hp : π (π⁻¹ p) = p := by
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    have hq : π (π⁻¹ q) = q := by
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    have h := hπ (π⁻¹ p) (π⁻¹ q)
    rw [hp, hq] at h
    exact h.symm

omit [DecidableEq I] [Fintype I] [∀ i, DecidableEq (B i)] [∀ i, Fintype (B i)] in
theorem blockPerm_property (π : blockPermSubgroup I B)
    (p q : (i : I) × B i) :
    ((π : Equiv.Perm ((i : I) × B i)) p).1
      = ((π : Equiv.Perm ((i : I) × B i)) q).1 ↔ p.1 = q.1 :=
  π.2 p q

/-- Generator images under a block-preserving permutation. -/
def blockPermGenerator (π : blockPermSubgroup I B) :
    Gen I B → BlockClifford I B :=
  Sum.elim (fun _ => sign I B) fun p =>
    lamp I B ((π : Equiv.Perm ((i : I) × B i)) p)

omit [DecidableEq I] [Fintype I] [(i : I) → DecidableEq (B i)] [(i : I) → Fintype (B i)] in
theorem blockPermGenerator_kills (π : blockPermSubgroup I B) :
    ∀ w ∈ relators I B,
      FreeGroup.lift (blockPermGenerator I B π) w = 1 := by
  intro w hw
  change IsRelator I B w at hw
  cases hw with
  | sign_sq =>
      rw [map_pow, FreeGroup.lift_apply_of]
      exact sign_sq I B
  | lamp_sq p =>
      rw [map_pow, FreeGroup.lift_apply_of]
      exact lamp_sq I B _
  | sign_comm p =>
      rw [map_commutatorElement, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of]
      exact (sign_commute_lamp I B _).commutator_eq
  | @braiding i b b' h =>
      rw [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      show ⁅lamp I B ((π : Equiv.Perm ((i : I) × B i)) ⟨i, b⟩),
          lamp I B ((π : Equiv.Perm ((i : I) × B i)) ⟨i, b'⟩)⁆ *
          (sign I B)⁻¹ = 1
      have hfst : ((π : Equiv.Perm ((i : I) × B i)) ⟨i, b⟩).1
          = ((π : Equiv.Perm ((i : I) × B i)) ⟨i, b'⟩).1 :=
        (blockPerm_property I B π _ _).mpr rfl
      have hne : (π : Equiv.Perm ((i : I) × B i)) ⟨i, b⟩
          ≠ (π : Equiv.Perm ((i : I) × B i)) ⟨i, b'⟩ := by
        intro hc
        exact h (sigma_mk_injective
          ((π : Equiv.Perm ((i : I) × B i)).injective hc))
      rw [commutator_lamp_lamp' I B hfst hne]
      exact mul_inv_cancel _

/-- The endomorphism induced by a block-preserving permutation. -/
def blockPermMap (π : blockPermSubgroup I B) :
    BlockClifford I B →* BlockClifford I B :=
  PresentedGroup.toGroup (blockPermGenerator_kills I B π)

omit [DecidableEq I] [Fintype I] [(i : I) → DecidableEq (B i)] [(i : I) → Fintype (B i)] in
@[simp] theorem blockPermMap_sign (π : blockPermSubgroup I B) :
    blockPermMap I B π (sign I B) = sign I B :=
  PresentedGroup.toGroup.of _

omit [DecidableEq I] [Fintype I] [(i : I) → DecidableEq (B i)] [(i : I) → Fintype (B i)] in
@[simp] theorem blockPermMap_lamp (π : blockPermSubgroup I B)
    (p : (i : I) × B i) :
    blockPermMap I B π (lamp I B p)
      = lamp I B ((π : Equiv.Perm ((i : I) × B i)) p) :=
  PresentedGroup.toGroup.of _

omit [DecidableEq I] [Fintype I] [(i : I) → DecidableEq (B i)] [(i : I) → Fintype (B i)] in
theorem blockPermMap_comp (π₁ π₂ : blockPermSubgroup I B)
    (g : BlockClifford I B) :
    blockPermMap I B π₁ (blockPermMap I B π₂ g)
      = blockPermMap I B (π₁ * π₂) g := by
  have h : (blockPermMap I B π₁).comp (blockPermMap I B π₂)
      = blockPermMap I B (π₁ * π₂) := by
    apply PresentedGroup.ext
    intro j
    match j with
    | Sum.inl () =>
        show blockPermMap I B π₁ (blockPermMap I B π₂ (sign I B))
          = blockPermMap I B (π₁ * π₂) (sign I B)
        rw [blockPermMap_sign, blockPermMap_sign, blockPermMap_sign]
    | Sum.inr p =>
        show blockPermMap I B π₁ (blockPermMap I B π₂ (lamp I B p))
          = blockPermMap I B (π₁ * π₂) (lamp I B p)
        rw [blockPermMap_lamp, blockPermMap_lamp, blockPermMap_lamp]
        rfl
  exact DFunLike.congr_fun h g

omit [DecidableEq I] [Fintype I] [(i : I) → DecidableEq (B i)] [(i : I) → Fintype (B i)] in
theorem blockPermMap_one_apply (g : BlockClifford I B) :
    blockPermMap I B 1 g = g := by
  have h : blockPermMap I B 1 = MonoidHom.id (BlockClifford I B) := by
    apply PresentedGroup.ext
    intro j
    match j with
    | Sum.inl () =>
        show blockPermMap I B 1 (sign I B) = sign I B
        rw [blockPermMap_sign]
    | Sum.inr p =>
        show blockPermMap I B 1 (lamp I B p) = lamp I B p
        rw [blockPermMap_lamp]
        rfl
  rw [h]
  rfl

/-- The automorphism induced by a block-preserving permutation. -/
def blockPermAut (π : blockPermSubgroup I B) :
    MulAut (BlockClifford I B) :=
  MonoidHom.toMulEquiv (blockPermMap I B π) (blockPermMap I B π⁻¹)
    (by
      apply PresentedGroup.ext
      intro j
      match j with
      | Sum.inl () =>
          show blockPermMap I B π⁻¹ (blockPermMap I B π (sign I B))
            = sign I B
          rw [blockPermMap_sign, blockPermMap_sign]
      | Sum.inr p =>
          show blockPermMap I B π⁻¹ (blockPermMap I B π (lamp I B p))
            = lamp I B p
          rw [blockPermMap_lamp, blockPermMap_lamp]
          simp)
    (by
      apply PresentedGroup.ext
      intro j
      match j with
      | Sum.inl () =>
          show blockPermMap I B π (blockPermMap I B π⁻¹ (sign I B))
            = sign I B
          rw [blockPermMap_sign, blockPermMap_sign]
      | Sum.inr p =>
          show blockPermMap I B π (blockPermMap I B π⁻¹ (lamp I B p))
            = lamp I B p
          rw [blockPermMap_lamp, blockPermMap_lamp]
          simp)

omit [DecidableEq I] [Fintype I] [(i : I) → DecidableEq (B i)] [(i : I) → Fintype (B i)] in
@[simp] theorem blockPermAut_apply (π : blockPermSubgroup I B)
    (g : BlockClifford I B) :
    blockPermAut I B π g = blockPermMap I B π g := rfl

/-- The action of block-preserving permutations by automorphisms. -/
def blockPermHom : blockPermSubgroup I B →* MulAut (BlockClifford I B) where
  toFun := blockPermAut I B
  map_one' := by
    apply MulEquiv.ext
    intro g
    rw [blockPermAut_apply, blockPermMap_one_apply]
    rfl
  map_mul' π₁ π₂ := by
    apply MulEquiv.ext
    intro g
    rw [blockPermAut_apply]
    show blockPermMap I B (π₁ * π₂) g
      = (blockPermAut I B π₁ * blockPermAut I B π₂) g
    rw [MulAut.mul_apply, blockPermAut_apply, blockPermAut_apply,
      blockPermMap_comp]

/-- **The abstract Lemma 3.1**: the semidirect product of the block
Clifford lamp group by any residually finite group acting through
block-preserving site permutations is residually finite.  The action has
finite range because the site set is finite. -/
theorem residuallyFinite_blockClifford_semidirect
    {Λ : Type} [Group Λ] [Group.ResiduallyFinite Λ]
    (α : Λ →* blockPermSubgroup I B) :
    Group.ResiduallyFinite
      (SemidirectProduct (BlockClifford I B) Λ
        ((blockPermHom I B).comp α)) := by
  haveI : Group.ResiduallyFinite (BlockClifford I B) :=
    residuallyFinite_blockClifford I B
  haveI : Finite ↥((blockPermHom I B).comp α).range := by
    have hfin : (Set.range ⇑(blockPermHom I B)).Finite :=
      Set.finite_range _
    have hsub : (((blockPermHom I B).comp α).range :
        Set (MulAut (BlockClifford I B)))
        ⊆ Set.range ⇑(blockPermHom I B) := by
      intro x hx
      obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hx
      exact ⟨α l, rfl⟩
    exact (hfin.subset hsub).to_subtype
  exact residuallyFinite_semidirectProduct_of_finite_range
    ((blockPermHom I B).comp α)

/-! ## Approximation corollaries -/

theorem isLEF_blockClifford : IsLEF (BlockClifford I B) := by
  haveI := residuallyFinite_blockClifford I B
  exact isLEF_of_residuallyFinite

theorem isSofic_blockClifford : IsSofic (BlockClifford I B) :=
  isSofic_of_isLEF (isLEF_blockClifford I B)

end BlockCliffordLamp
end GroupApproximation
