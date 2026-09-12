import Mathlib.GroupTheory.IsPerfect

/-!
# Algebra of central covers

This file isolates algebraic mechanisms for central covers.
If an element centralizes a perfect quotient of a group modulo a central
kernel, then it already centralizes the whole group.  Applied to the full
inverse image of a Kun--Thom subgroup, this lifts a strict centralizer witness
through a central extension.  No approximation-theoretic theorem is accepted
as a premise here.
-/

namespace GroupApproximation

open Subgroup
open scoped commutatorElement

/-- A surjective group homomorphism with central kernel. -/
structure CentralExtension (E H : Type*) [Group E] [Group H] where
  projection : E →* H
  surjective : Function.Surjective projection
  ker_le_center : projection.ker ≤ Subgroup.center E

namespace CentralExtension

variable {E H : Type*} [Group E] [Group H]

/-- Transport a central extension across an isomorphism of its base. -/
def postcompEquiv {K : Type*} [Group K] (P : CentralExtension E H)
    (e : H ≃* K) : CentralExtension E K where
  projection := e.toMonoidHom.comp P.projection
  surjective := e.surjective.comp P.surjective
  ker_le_center := by
    intro x hx
    apply P.ker_le_center
    rw [MonoidHom.mem_ker]
    have hx' : e (P.projection x) = 1 := by
      change e.toMonoidHom (P.projection x) = 1
      exact MonoidHom.mem_ker.mp hx
    apply e.injective
    rw [map_one]
    exact hx'

theorem commutator_mem_center (P : CentralExtension E H) {x y : E}
    (h : Commute (P.projection x) (P.projection y)) :
    ⁅x, y⁆ ∈ Subgroup.center E := by
  apply P.ker_le_center
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact h.commutator_eq

/-- The full inverse image of a subgroup under a central extension. -/
def preimage (P : CentralExtension E H) (G : Subgroup H) : Subgroup E :=
  G.comap P.projection

/-- The projection from the full inverse image onto the original subgroup. -/
def preimageProjection (P : CentralExtension E H) (G : Subgroup H) :
    P.preimage G →* G where
  toFun x := ⟨P.projection x, x.property⟩
  map_one' := Subtype.ext P.projection.map_one
  map_mul' x y := Subtype.ext (P.projection.map_mul x y)

@[simp] theorem preimageProjection_apply (P : CentralExtension E H)
    (G : Subgroup H) (x : P.preimage G) :
    ((P.preimageProjection G x : G) : H) = P.projection x := rfl

theorem preimageProjection_surjective (P : CentralExtension E H)
    (G : Subgroup H) : Function.Surjective (P.preimageProjection G) := by
  intro g
  obtain ⟨x, hx⟩ := P.surjective g
  refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
  change P.projection x ∈ G
  rw [hx]
  exact g.property

/-- The full inverse image of `Γ ≤ G` inside the full inverse image of `G`. -/
def liftedSubgroup (P : CentralExtension E H) (G : Subgroup H)
    (Γ : Subgroup G) : Subgroup (P.preimage G) :=
  Γ.comap (P.preimageProjection G)

/-- The natural quotient map from the lifted subgroup to `Γ`. -/
def liftedProjection (P : CentralExtension E H) (G : Subgroup H)
    (Γ : Subgroup G) : P.liftedSubgroup G Γ →* Γ where
  toFun x := ⟨P.preimageProjection G x, x.property⟩
  map_one' := by
    apply Subtype.ext
    exact (P.preimageProjection G).map_one
  map_mul' x y := Subtype.ext ((P.preimageProjection G).map_mul x y)

@[simp] theorem liftedProjection_apply (P : CentralExtension E H)
    (G : Subgroup H) (Γ : Subgroup G) (x : P.liftedSubgroup G Γ) :
    ((P.liftedProjection G Γ x : Γ) : G) = P.preimageProjection G x := by
  change P.preimageProjection G (x : P.preimage G) = P.preimageProjection G x
  rfl

theorem liftedProjection_surjective (P : CentralExtension E H)
    (G : Subgroup H) (Γ : Subgroup G) :
    Function.Surjective (P.liftedProjection G Γ) := by
  intro γ
  obtain ⟨x, hx⟩ := P.preimageProjection_surjective G γ
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change P.preimageProjection G x ∈ Γ
    rw [hx]
    exact γ.property
  · apply Subtype.ext
    simpa only [liftedProjection_apply] using hx

/-- The inclusion of a lifted subgroup into the covering group. -/
def liftedInclusion (P : CentralExtension E H) (G : Subgroup H)
    (Γ : Subgroup G) : P.liftedSubgroup G Γ →* E :=
  (P.preimage G).subtype.comp (P.liftedSubgroup G Γ).subtype

@[simp] theorem projection_liftedInclusion (P : CentralExtension E H)
    (G : Subgroup H) (Γ : Subgroup G) (x : P.liftedSubgroup G Γ) :
    P.projection (P.liftedInclusion G Γ x) =
      G.subtype (P.liftedProjection G Γ x) := by
  change P.projection (x : E) =
    G.subtype (P.preimageProjection G (x : P.preimage G))
  rfl

end CentralExtension

section PerfectCentralizer

variable {L Γ E : Type*} [Group L] [Group Γ] [Group E]

/-- The commutator with `a`, valued in the center.  Centrality is precisely
what turns the usual crossed-homomorphism formula into a homomorphism. -/
def centralCommutatorHom (j : L →* E) (a : E)
    (hcentral : ∀ x : L, ⁅a, j x⁆ ∈ Subgroup.center E) :
    L →* Subgroup.center E where
  toFun x := ⟨⁅a, j x⁆, hcentral x⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [map_mul]
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hc := Subgroup.mem_center_iff.mp (hcentral y) (j x)
    rw [mul_assoc ⁅a, j x⁆ (j x) ⁅a, j y⁆]
    rw [hc]
    group

@[simp] theorem centralCommutatorHom_apply (j : L →* E) (a : E)
    (hcentral : ∀ x : L, ⁅a, j x⁆ ∈ Subgroup.center E) (x : L) :
    (centralCommutatorHom j a hcentral x : E) = ⁅a, j x⁆ := rfl

/-- **Perfect-quotient centralizer lifting.**  Let `q : L → Γ` be onto
with perfect target.  If the commutators `[a,j(x)]` are central and vanish on
`ker q`, then they vanish everywhere.  Equivalently, `a` centralizes `j(L)`.

This is the finite-cover argument stripped to its reusable algebraic core;
neither finiteness of the kernel nor finiteness of either group is needed. -/
theorem commute_of_perfect_quotient [Group.IsPerfect Γ]
    (q : L →* Γ) (hq : Function.Surjective q)
    (j : L →* E) (a : E)
    (hcentral : ∀ x : L, ⁅a, j x⁆ ∈ Subgroup.center E)
    (hker : ∀ x : L, q x = 1 → Commute a (j x)) :
    ∀ x : L, Commute a (j x) := by
  let φ : L →* Subgroup.center E := centralCommutatorHom j a hcentral
  have hmap : (commutator L).map q = commutator Γ := by
    rw [map_commutator_eq, q.range_eq_top_of_surjective hq, _root_.commutator_def]
  have hderived : commutator L ≤ φ.ker := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨u, v, rfl⟩
    change φ ⁅u, v⁆ = 1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_commute.mpr
    apply Subtype.coe_injective
    exact (Subgroup.mem_center_iff.mp (φ u).property (φ v : E)).symm
  intro x
  have hqx : q x ∈ (commutator L).map q := by
    rw [hmap]
    exact Group.IsPerfect.mem_commutator
  obtain ⟨y, hy, hyq⟩ := hqx
  let z : L := x * y⁻¹
  have hzq : q z = 1 := by
    dsimp [z]
    rw [map_mul, map_inv, hyq]
    simp
  have hφz : φ z = 1 := by
    apply Subtype.ext
    change ⁅a, j z⁆ = 1
    exact commutatorElement_eq_one_iff_commute.mpr (hker z hzq)
  have hφy : φ y = 1 := hderived hy
  have hx : z * y = x := by
    dsimp [z]
    group
  apply commutatorElement_eq_one_iff_commute.mp
  change (φ x : E) = 1
  rw [← hx, map_mul, hφz, hφy, one_mul]
  rfl

end PerfectCentralizer

section PerfectCentralQuotient

variable {A B : Type*} [Group A] [Group B]

/-- A subgroup of a perfect group which still surjects through a central
quotient is the whole group.  This is the algebraic step used in the
universal-cover argument: lifted compressors generate a subgroup mapping
onto the base, and perfectness removes the remaining central factor. -/
theorem subgroup_eq_top_of_surjects_mod_central [Group.IsPerfect A]
    (f : A →* B) (L : Subgroup A)
    (hL : ∀ b : B, ∃ l : L, f l = b)
    (hker : f.ker ≤ Subgroup.center A) : L = ⊤ := by
  have hdecomp : ∀ g : A, ∃ l : L, ∃ z : A,
      z ∈ Subgroup.center A ∧ g = (l : A) * z := by
    intro g
    obtain ⟨l, hl⟩ := hL (f g)
    let z : A := (l : A)⁻¹ * g
    have hzker : z ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      dsimp [z]
      rw [map_mul, map_inv, hl]
      simp
    have hzcenter : z ∈ Subgroup.center A := hker hzker
    have hg : g = (l : A) * z := by
      dsimp [z]
      group
    exact ⟨l, z, hzcenter, hg⟩
  apply top_unique
  have hcomm : commutator A ≤ L := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨g, h, rfl⟩
    obtain ⟨l, z, hz, rfl⟩ := hdecomp g
    obtain ⟨m, w, hw, rfl⟩ := hdecomp h
    have hzc : Commute z ((m : A) * w) :=
      (Subgroup.mem_center_iff.mp hz ((m : A) * w)).symm
    have hwc : Commute (l : A) w :=
      Subgroup.mem_center_iff.mp hw (l : A)
    rw [commutatorElement_mul_left_eq_conj_mul, hzc.commutator_eq]
    simp only [mul_one, mul_inv_cancel, one_mul]
    rw [commutatorElement_mul_right_eq_mul_conj,
      hwc.commutator_eq]
    simp only [mul_one, mul_inv_cancel_right]
    change (l : A) * m * (l : A)⁻¹ * m⁻¹ ∈ L
    exact L.mul_mem
      (L.mul_mem (L.mul_mem l.property m.property) (L.inv_mem l.property))
      (L.inv_mem m.property)
  simpa using hcomm

end PerfectCentralQuotient

namespace CentralExtension

variable {E H : Type} [Group E] [Group H]

/-- A lift of an element centralizing a perfect subgroup downstairs
centralizes the entire full inverse image of that subgroup upstairs. -/
theorem lift_centralizes_perfect_preimage (P : CentralExtension E H)
    (G : Subgroup H) (Γ : Subgroup G) [Group.IsPerfect Γ]
    (a : E)
    (ha : ∀ g : G, g ∈ Γ → Commute (P.projection a) (G.subtype g)) :
    ∀ x : P.liftedSubgroup G Γ, Commute a (P.liftedInclusion G Γ x) := by
  apply commute_of_perfect_quotient
      (P.liftedProjection G Γ) (P.liftedProjection_surjective G Γ)
      (P.liftedInclusion G Γ) a
  · intro x
    apply P.commutator_mem_center
    simpa using ha (P.liftedProjection G Γ x)
      (P.liftedProjection G Γ x).property
  · intro x hx
    have hpx : P.projection (P.liftedInclusion G Γ x) = 1 := by
      have hx' := congrArg (fun y : Γ ↦ G.subtype (y : G)) hx
      simpa using hx'
    have hcenter : P.liftedInclusion G Γ x ∈ Subgroup.center E :=
      P.ker_le_center (MonoidHom.mem_ker.mpr hpx)
    exact Subgroup.mem_center_iff.mp hcenter a

/-! ## A good subcover inside an arbitrary central extension -/

/-- The projection of a subgroup of the full inverse image onto the base
subgroup.  Surjectivity is an extra hypothesis: it is the property supplied
by the image of a universal or stem cover. -/
def subcoverProjection (P : CentralExtension E H) (G : Subgroup H)
    (L : Subgroup (P.preimage G)) : L →* G :=
  (P.preimageProjection G).comp L.subtype

/-- The inverse image of `Γ` in a chosen subcover `L`. -/
def subcoverLiftedSubgroup (P : CentralExtension E H) (G : Subgroup H)
    (Γ : Subgroup G) (L : Subgroup (P.preimage G)) : Subgroup L :=
  Γ.comap (P.subcoverProjection G L)

/-- The quotient map from the lifted subgroup in a subcover onto `Γ`. -/
def subcoverLiftedProjection (P : CentralExtension E H) (G : Subgroup H)
    (Γ : Subgroup G) (L : Subgroup (P.preimage G)) :
    P.subcoverLiftedSubgroup G Γ L →* Γ where
  toFun x := ⟨P.subcoverProjection G L x, x.property⟩
  map_one' := by
    apply Subtype.ext
    exact (P.subcoverProjection G L).map_one
  map_mul' x y := Subtype.ext ((P.subcoverProjection G L).map_mul x y)

@[simp] theorem subcoverLiftedProjection_apply
    (P : CentralExtension E H) (G : Subgroup H) (Γ : Subgroup G)
    (L : Subgroup (P.preimage G)) (x : P.subcoverLiftedSubgroup G Γ L) :
    ((P.subcoverLiftedProjection G Γ L x : Γ) : G) =
      P.subcoverProjection G L x := by
  change P.subcoverProjection G L (x : L) = P.subcoverProjection G L x
  rfl

theorem subcoverLiftedProjection_surjective
    (P : CentralExtension E H) (G : Subgroup H) (Γ : Subgroup G)
    (L : Subgroup (P.preimage G))
    (hL : Function.Surjective (P.subcoverProjection G L)) :
    Function.Surjective (P.subcoverLiftedProjection G Γ L) := by
  intro γ
  obtain ⟨x, hx⟩ := hL γ
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change P.subcoverProjection G L x ∈ Γ
    rw [hx]
    exact γ.property
  · apply Subtype.ext
    simpa only [subcoverLiftedProjection_apply] using hx

/-- Inclusion of a chosen subcover into the ambient central extension. -/
def subcoverInclusion (P : CentralExtension E H) (G : Subgroup H)
    (L : Subgroup (P.preimage G)) : L →* E :=
  (P.preimage G).subtype.comp L.subtype

@[simp] theorem projection_subcoverInclusion
    (P : CentralExtension E H) (G : Subgroup H)
    (L : Subgroup (P.preimage G)) (x : L) :
    P.projection (P.subcoverInclusion G L x) =
      G.subtype (P.subcoverProjection G L x) := by
  change P.projection (x : E) =
    G.subtype (P.preimageProjection G (x : P.preimage G))
  rfl

/-- A lift of a centralizer downstairs centralizes the lifted perfect
subgroup in every surjective subcover. -/
theorem lift_centralizes_perfect_subcover (P : CentralExtension E H)
    (G : Subgroup H) (Γ : Subgroup G) [Group.IsPerfect Γ]
    (L : Subgroup (P.preimage G))
    (hL : Function.Surjective (P.subcoverProjection G L))
    (a : E)
    (ha : ∀ g : G, g ∈ Γ → Commute (P.projection a) (G.subtype g)) :
    ∀ x : P.subcoverLiftedSubgroup G Γ L,
      Commute a (P.subcoverInclusion G L x) := by
  apply commute_of_perfect_quotient
      (P.subcoverLiftedProjection G Γ L)
      (P.subcoverLiftedProjection_surjective G Γ L hL)
      ((P.subcoverInclusion G L).comp
        (P.subcoverLiftedSubgroup G Γ L).subtype) a
  · intro x
    apply P.commutator_mem_center
    simpa using ha (P.subcoverLiftedProjection G Γ L x)
      (P.subcoverLiftedProjection G Γ L x).property
  · intro x hx
    have hpx : P.projection (P.subcoverInclusion G L x) = 1 := by
      have hx' := congrArg (fun y : Γ ↦ G.subtype (y : G)) hx
      simpa using hx'
    have hcenter : P.subcoverInclusion G L x ∈ Subgroup.center E :=
      P.ker_le_center (MonoidHom.mem_ker.mpr hpx)
    exact Subgroup.mem_center_iff.mp hcenter a

end CentralExtension

end GroupApproximation
