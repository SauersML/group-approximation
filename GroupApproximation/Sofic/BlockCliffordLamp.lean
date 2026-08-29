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

variable (I : Type)
variable (B : I → Type)

/-! ## Commuting-involution products

A family of pairwise commuting involutions in any group receives a
homomorphism from the corresponding sign group, sending a sign vector to
the product of the involutions in its support. -/

section SignProd

variable {G : Type*} [Group G] {β : Type}
variable (t : β → G) (hcomm : ∀ a b, Commute (t a) (t b))

/-- The support of a sign vector, as a finset. -/
def sset [Fintype β] (ε : β → Multiplicative (ZMod 2)) : Finset β :=
  Finset.univ.filter fun b => Multiplicative.toAdd (ε b) = 1

theorem sset_one [Fintype β] :
    sset (1 : β → Multiplicative (ZMod 2)) = ∅ := by
  rw [sset, Finset.filter_eq_empty_iff]
  intro b _
  simp only [Pi.one_apply, toAdd_one]
  decide

theorem sset_mul [Fintype β] [DecidableEq β]
    (ε ε' : β → Multiplicative (ZMod 2)) :
    sset (ε * ε') = sset ε ∆ sset ε' := by
  have hxor : ∀ a b : ZMod 2, a + b = 1 ↔
      ((a = 1 ∧ ¬b = 1) ∨ (¬a = 1 ∧ b = 1)) := by decide
  ext b
  simp only [sset, Finset.mem_symmDiff, mem_filter, mem_univ, true_and]
  have : Multiplicative.toAdd ((ε * ε') b)
      = Multiplicative.toAdd (ε b) + Multiplicative.toAdd (ε' b) := rfl
  rw [this, hxor]
  grind

/-- The product of the involutions over a finset. -/
def prodOf (s : Finset β) : G :=
  s.noncommProd t fun a _ b _ _ => hcomm a b

theorem prodOf_empty : prodOf t hcomm (∅ : Finset β) = 1 :=
  Finset.noncommProd_empty _ _

theorem prodOf_singleton (b : β) : prodOf t hcomm {b} = t b :=
  Finset.noncommProd_singleton _ _

theorem prodOf_union [DecidableEq β] {s u : Finset β} (h : Disjoint s u) :
    prodOf t hcomm (s ∪ u) = prodOf t hcomm s * prodOf t hcomm u :=
  Finset.noncommProd_union_of_disjoint h _ _

theorem commute_prodOf (g : G) (hg : ∀ b, Commute g (t b))
    (s : Finset β) : Commute g (prodOf t hcomm s) :=
  Finset.noncommProd_commute _ _ _ _ fun b _ => hg b

theorem prodOf_commute (s u : Finset β) :
    Commute (prodOf t hcomm s) (prodOf t hcomm u) :=
  commute_prodOf t hcomm (prodOf t hcomm s)
    (fun b ↦ (commute_prodOf t hcomm (t b) (fun a ↦ hcomm b a) s).symm) u

theorem prodOf_sq [DecidableEq β] (hsq : ∀ b, t b * t b = 1)
    (s : Finset β) :
    prodOf t hcomm s * prodOf t hcomm s = 1 := by
  induction s using Finset.induction_on with
  | empty => rw [prodOf_empty, one_mul]
  | insert a s ha ih =>
      rw [prodOf, Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
      show t a * prodOf t hcomm s * (t a * prodOf t hcomm s) = 1
      calc t a * prodOf t hcomm s * (t a * prodOf t hcomm s)
          = t a * (prodOf t hcomm s * t a) * prodOf t hcomm s := by
            group
        _ = t a * (t a * prodOf t hcomm s) * prodOf t hcomm s := by
            rw [(commute_prodOf t hcomm (t a) (fun b => hcomm a b) s).symm.eq]
        _ = (t a * t a) * (prodOf t hcomm s * prodOf t hcomm s) := by
            group
        _ = 1 := by rw [hsq a, ih, one_mul]

theorem prodOf_symmDiff [DecidableEq β] (hsq : ∀ b, t b * t b = 1)
    (s u : Finset β) :
    prodOf t hcomm (s ∆ u) = prodOf t hcomm s * prodOf t hcomm u := by
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
  calc prodOf t hcomm (s \ u) * prodOf t hcomm (u \ s)
      = prodOf t hcomm (s \ u) * prodOf t hcomm (u \ s) *
          (prodOf t hcomm (s ∩ u) * prodOf t hcomm (s ∩ u)) := by
        rw [prodOf_sq t hcomm hsq (s ∩ u), mul_one]
    _ = prodOf t hcomm (s \ u) *
          (prodOf t hcomm (u \ s) * prodOf t hcomm (s ∩ u)) *
          prodOf t hcomm (s ∩ u) := by group
    _ = prodOf t hcomm (s \ u) *
          (prodOf t hcomm (s ∩ u) * prodOf t hcomm (u \ s)) *
          prodOf t hcomm (s ∩ u) := by rw [(prodOf_commute t hcomm _ _).eq]
    _ = prodOf t hcomm (s \ u) * prodOf t hcomm (s ∩ u) *
          (prodOf t hcomm (u \ s) * prodOf t hcomm (s ∩ u)) := by group

/-- The homomorphism from the sign group determined by a family of
pairwise commuting involutions. -/
def signProdHom [Fintype β] [DecidableEq β]
    (hsq : ∀ b, t b * t b = 1) :
    (β → Multiplicative (ZMod 2)) →* G where
  toFun ε := prodOf t hcomm (sset ε)
  map_one' := by rw [sset_one, prodOf_empty]
  map_mul' ε ε' := by
    rw [sset_mul, prodOf_symmDiff t hcomm hsq]

@[simp]
theorem signProdHom_apply (hsq : ∀ b, t b * t b = 1)
    [Fintype β] [DecidableEq β]
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

theorem sign_sq : sign I B ^ 2 = 1 := by
  have := PresentedGroup.one_of_mem (IsRelator.sign_sq (I := I) (B := B))
  rwa [map_pow] at this

theorem lamp_sq (p : (i : I) × B i) : lamp I B p ^ 2 = 1 := by
  have := PresentedGroup.one_of_mem (IsRelator.lamp_sq (I := I) (B := B) p)
  rwa [map_pow] at this

theorem sign_commute_lamp (p : (i : I) × B i) :
    Commute (sign I B) (lamp I B p) := by
  have := PresentedGroup.one_of_mem
    (IsRelator.sign_comm (I := I) (B := B) p)
  rw [map_commutatorElement] at this
  exact commutatorElement_eq_one_iff_commute.mp this

theorem commutator_lamp_lamp {i : I} {b b' : B i} (h : b ≠ b') :
    ⁅lamp I B ⟨i, b⟩, lamp I B ⟨i, b'⟩⁆ = sign I B := by
  have h1 := PresentedGroup.one_of_mem
    (IsRelator.braiding (I := I) (B := B) h)
  rw [map_mul, map_inv, map_commutatorElement] at h1
  change ⁅lamp I B ⟨i, b⟩, lamp I B ⟨i, b'⟩⁆ * (sign I B)⁻¹ = 1 at h1
  calc ⁅lamp I B ⟨i, b⟩, lamp I B ⟨i, b'⟩⁆
      = ⁅lamp I B ⟨i, b⟩, lamp I B ⟨i, b'⟩⁆ * (sign I B)⁻¹ * sign I B := by
        group
    _ = 1 * sign I B := by rw [h1]
    _ = sign I B := one_mul _

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

theorem sign_mem_center : sign I B ∈ Subgroup.center (BlockClifford I B) :=
  Subgroup.mem_center_iff.mpr fun g => ((sign_commute I B g).symm).eq

/-! ## The detector: the complete Clifford lamp group on all sites -/

/-- Generator images in the complete Clifford lamp group: impose the
missing cross-block anticommutation relations. -/
def fullGenerator : Gen I B → CliffordLamp.LampGroup ((i : I) × B i) :=
  Sum.elim (fun _ => CliffordLamp.sign _) fun p => CliffordLamp.lamp _ p

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

/-! ## The free-product quotient -/

/-- One coordinate flip in the sign group of block `i`. -/
def coordFlip (i : I) [DecidableEq (B i)] (b : B i) : SignGroup B i :=
  fun b' => if b' = b then Multiplicative.ofAdd 1 else 1

theorem coordFlip_mul_self (i : I) [DecidableEq (B i)] (b : B i) :
    coordFlip I B i b * coordFlip I B i b = 1 := by
  funext b'
  by_cases hb : b' = b <;>
    simp only [coordFlip, Pi.mul_apply, Pi.one_apply, hb, if_true, if_false] <;>
    decide

theorem sset_coordFlip (i : I) [DecidableEq (B i)] [Fintype (B i)]
    (b : B i) :
    sset (β := B i) (coordFlip I B i b) = {b} := by
  ext b'
  by_cases h : b' = b <;> simp [sset, coordFlip, h]

/-! ## The section and injectivity of the descended quotient map -/

/-! ## The finite detector and the conclusion -/

/-! ## Block-preserving permutations act on the block Clifford group -/

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

/-! ## Approximation corollaries -/

end BlockCliffordLamp
end GroupApproximation
