import Mathlib.GroupTheory.IsPerfect
import NonsoficGroupsExist.Sofic.FreeLampReduction

/-!
# Central-cover inheritance of Kun--Thom witnesses

This file isolates the algebraic mechanism behind central-cover inheritance.
If an element centralizes a perfect quotient of a group modulo a central
kernel, then it already centralizes the whole group.  Applied to the full
inverse image of a Kun--Thom subgroup, this lifts a strict centralizer witness
through a central extension.

The analytic input remains exactly the named
`CentralizerNormalization` hypothesis from `FreeLampReduction`; no new
approximation-theoretic axiom is introduced here.
-/

namespace NonsoficGroupsExist

open Subgroup
open scoped commutatorElement

/-- A surjective group homomorphism with central kernel. -/
structure CentralExtension (E H : Type*) [Group E] [Group H] where
  projection : E →* H
  surjective : Function.Surjective projection
  ker_le_center : projection.ker ≤ Subgroup.center E

namespace CentralExtension

variable {E H : Type*} [Group E] [Group H]

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

/-- **Central-cover inheritance of a strict Kun--Thom witness.**

Let `G ≤ H` contain a perfect subgroup `Γ`, and let an element `a ∈ H`
centralize `Γ` but fail to centralize one inverse conjugate `t⁻¹γt`.
For any countable central extension `E → H`, if the lifted pair satisfies the
same named Kun--Thom centralizer-normalization hypothesis, then `E` is
nonsofic.

The central kernel may be infinite.  The only role of the usual finite-cover
hypothesis is to establish `CentralizerNormalization` for the lifted pair;
the inheritance argument itself does not use finiteness. -/
theorem not_isSofic_of_centralExtension_strictWitness
    (P : CentralExtension E H) [Countable E]
    (G : Subgroup H) (Γ : Subgroup G) [Group.IsPerfect Γ]
    (hcn : CentralizerNormalization (P.preimage G) (P.liftedSubgroup G Γ))
    (a : H) (ha : ∀ g : G, g ∈ Γ → Commute a (G.subtype g))
    {t γ : G} (hγ : γ ∈ Γ)
    (hstrict : ¬ Commute a (G.subtype (t⁻¹ * γ * t))) :
    ¬ IsSofic E := by
  obtain ⟨aLift, haLift⟩ := P.surjective a
  obtain ⟨tLift, htLift⟩ := P.preimageProjection_surjective G t
  obtain ⟨gammaLift, hgammaLift⟩ :=
    P.liftedProjection_surjective G Γ ⟨γ, hγ⟩
  apply not_isSofic_of_strictCentralizerWitness
      (P.liftedSubgroup G Γ) hcn (P.preimage G).subtype
      Subtype.val_injective aLift (t := tLift)
      (γ := (gammaLift : P.preimage G))
  · intro x hx
    exact P.lift_centralizes_perfect_preimage G Γ aLift
      (by
        intro g hg
        rw [haLift]
        exact ha g hg)
      ⟨x, hx⟩
  · exact gammaLift.property
  · intro hcomm
    apply hstrict
    have hmapped := hcomm.map P.projection
    have htProj : P.projection ((P.preimage G).subtype tLift) = G.subtype t := by
      change G.subtype (P.preimageProjection G tLift) = G.subtype t
      exact congrArg G.subtype htLift
    have hgammaProj :
        P.projection ((P.preimage G).subtype (gammaLift : P.preimage G)) =
          G.subtype γ := by
      change G.subtype (P.preimageProjection G (gammaLift : P.preimage G)) =
        G.subtype γ
      have h := congrArg (fun g : Γ ↦ G.subtype (g : G)) hgammaLift
      simpa only [liftedProjection_apply] using h
    change Commute a
      ((G.subtype t)⁻¹ * G.subtype γ * G.subtype t)
    simpa only [map_mul, map_inv, haLift, htProj, hgammaProj] using hmapped

end CentralExtension

end NonsoficGroupsExist
