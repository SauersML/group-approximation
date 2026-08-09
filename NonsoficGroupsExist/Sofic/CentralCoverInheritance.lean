import Mathlib.GroupTheory.IsPerfect
import NonsoficGroupsExist.Sofic.FreeLampReduction
import NonsoficGroupsExist.Sofic.KazhdanCorner

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

/-- **Subcover form of central-cover inheritance.**  An arbitrary countable
central extension is nonsofic as soon as it contains a surjective subcover
whose lifted pair has Kun--Thom centralizer normalization.  This is the form
used with the finite image of a universal/stem cover; the ambient central
kernel can still be infinite. -/
theorem not_isSofic_of_centralExtension_subcoverWitness
    (P : CentralExtension E H) [Countable E]
    (G : Subgroup H) (Γ : Subgroup G) [Group.IsPerfect Γ]
    (L : Subgroup (P.preimage G))
    (hL : Function.Surjective (P.subcoverProjection G L))
    (hcn : CentralizerNormalization L (P.subcoverLiftedSubgroup G Γ L))
    (a : H) (ha : ∀ g : G, g ∈ Γ → Commute a (G.subtype g))
    {t γ : G} (hγ : γ ∈ Γ)
    (hstrict : ¬ Commute a (G.subtype (t⁻¹ * γ * t))) :
    ¬ IsSofic E := by
  obtain ⟨aLift, haLift⟩ := P.surjective a
  obtain ⟨tLift, htLift⟩ := hL t
  obtain ⟨gammaLift, hgammaLift⟩ :=
    P.subcoverLiftedProjection_surjective G Γ L hL ⟨γ, hγ⟩
  apply not_isSofic_of_strictCentralizerWitness
      (P.subcoverLiftedSubgroup G Γ L) hcn
      (P.subcoverInclusion G L) (by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        exact hxy)
      aLift (t := tLift) (γ := (gammaLift : L))
  · intro x hx
    exact P.lift_centralizes_perfect_subcover G Γ L hL aLift
      (by
        intro g hg
        rw [haLift]
        exact ha g hg)
      ⟨x, hx⟩
  · exact gammaLift.property
  · intro hcomm
    apply hstrict
    have hmapped := hcomm.map P.projection
    have htProj : P.projection (P.subcoverInclusion G L tLift) = G.subtype t := by
      rw [projection_subcoverInclusion]
      exact congrArg G.subtype htLift
    have hgammaProj :
        P.projection (P.subcoverInclusion G L (gammaLift : L)) =
          G.subtype γ := by
      rw [projection_subcoverInclusion]
      have h := congrArg (fun g : Γ ↦ G.subtype (g : G)) hgammaLift
      simpa only [subcoverLiftedProjection_apply] using h
    change Commute a
      ((G.subtype t)⁻¹ * G.subtype γ * G.subtype t)
    simpa only [map_mul, map_inv, haLift, htProj, hgammaProj] using hmapped

/-- The universal/stem-cover certificate: every countable central extension
contains some subgroup surjecting onto `G` for which the lifted pair has the
Kun--Thom normalization property.  In the intended application, `L` is the
finite image of a universal central extension, and finiteness of the Schur
multiplier is used only to produce this certificate. -/
def CentralSubcoverStableNormalization (H : Type) [Group H]
    (G : Subgroup H) (Γ : Subgroup G) : Prop :=
  ∀ (E : Type) [Group E] [Countable E] (P : CentralExtension E H),
    ∃ L : Subgroup (P.preimage G),
      Function.Surjective (P.subcoverProjection G L) ∧
        CentralizerNormalization L (P.subcoverLiftedSubgroup G Γ L)

/-- **Arbitrary-kernel subcover theorem.**  A strict witness for a perfect
pair, together with the universal/stem-cover certificate, makes every
countable central extension nonsofic.  Unlike the full-preimage formulation,
normalization is required only on one good subcover; this is what permits an
arbitrary infinite ambient central kernel. -/
theorem allCentralExtensions_not_isSofic_of_subcoverStrictWitness
    {H : Type} [Group H]
    (G : Subgroup H) (Γ : Subgroup G) [Group.IsPerfect Γ]
    (hstable : CentralSubcoverStableNormalization H G Γ)
    (a : H) (ha : ∀ g : G, g ∈ Γ → Commute a (G.subtype g))
    {t γ : G} (hγ : γ ∈ Γ)
    (hstrict : ¬ Commute a (G.subtype (t⁻¹ * γ * t)))
    {E : Type} [Group E] [Countable E] (P : CentralExtension E H) :
    ¬ IsSofic E := by
  obtain ⟨L, hL, hcn⟩ := hstable E P
  exact P.not_isSofic_of_centralExtension_subcoverWitness
    G Γ L hL hcn a ha hγ hstrict

/-- The exact external stability certificate needed to turn the one-cover
inheritance theorem into a statement about *all* central covers.  For a
stable Kun--Thom pair this is supplied by applying the cited normalization
theorem to every lifted pair.  Keeping it named prevents that citation from
being silently conflated with the algebraic inheritance proof. -/
def CentralCoverStableNormalization (H : Type) [Group H]
    (G : Subgroup H) (Γ : Subgroup G) : Prop :=
  ∀ (E : Type) [Group E] [Countable E] (P : CentralExtension E H),
    CentralizerNormalization (P.preimage G) (P.liftedSubgroup G Γ)

/-- **All-central-covers form.**  A strict witness for a perfect pair whose
Kun--Thom normalization is stable under central covers makes every countable
central extension nonsofic.  No finiteness assumption is imposed on the
central kernel. -/
theorem allCentralExtensions_not_isSofic_of_strictWitness
    {H : Type} [Group H]
    (G : Subgroup H) (Γ : Subgroup G) [Group.IsPerfect Γ]
    (hstable : CentralCoverStableNormalization H G Γ)
    (a : H) (ha : ∀ g : G, g ∈ Γ → Commute a (G.subtype g))
    {t γ : G} (hγ : γ ∈ Γ)
    (hstrict : ¬ Commute a (G.subtype (t⁻¹ * γ * t)))
    {E : Type} [Group E] [Countable E] (P : CentralExtension E H) :
    ¬ IsSofic E :=
  P.not_isSofic_of_centralExtension_strictWitness G Γ
    (hstable E P) a ha hγ hstrict

end CentralExtension

/-! ## The Steinberg-target weak-MF endpoint -/

/-- Every nontrivial quotient of `J` is nonsofic.  For a quasisimple
universal central cover this follows once all of the intervening central
covers of the simple base are known to be nonsofic. -/
def EveryNontrivialQuotientIsNonsofic (J : Type) [Group J] : Prop :=
  ∀ (Q : Type) (_ : Group Q) (q : J →* Q),
    Function.Surjective q → (∃ g : J, q g ≠ 1) → ¬ IsSofic Q

/-- Every homomorphism from `J` to a sofic group is trivial.  Unlike a
statement merely forbidding embeddings, this rules out every nontrivial
sofic image of `J`. -/
def HasNoNontrivialSoficImage (J : Type) [Group J] : Prop :=
  ∀ (S : Type) (_ : Group S), IsSofic S →
    ∀ (f : J →* S) (g : J), f g = 1

/-- If every nontrivial quotient of `J` is nonsofic, then every map from `J`
to a sofic group is trivial: its range is both a quotient of `J` and a
subgroup of the sofic target. -/
theorem hasNoNontrivialSoficImage_of_everyNontrivialQuotientIsNonsofic
    {J : Type} [Group J]
    (hquot : EveryNontrivialQuotientIsNonsofic J) :
    HasNoNontrivialSoficImage J := by
  intro S hSGroup hS f g
  letI : Group S := hSGroup
  by_contra hfg
  have hgne : f.rangeRestrict g ≠ 1 := by
    intro hg
    apply hfg
    exact congrArg Subtype.val hg
  have hrange : IsSofic f.range :=
    isSofic_of_injective f.range.subtype Subtype.val_injective hS
  exact (hquot f.range inferInstance f.rangeRestrict
    f.rangeRestrict_surjective ⟨g, hgne⟩) hrange

/-- Conversely, absence of nontrivial sofic images makes every nontrivial
quotient nonsofic, since a quotient map itself would otherwise be a
nontrivial map to a sofic group. -/
theorem everyNontrivialQuotientIsNonsofic_of_hasNoNontrivialSoficImage
    {J : Type} [Group J]
    (himage : HasNoNontrivialSoficImage J) :
    EveryNontrivialQuotientIsNonsofic J := by
  intro Q hQGroup q _ ⟨g, hg⟩ hQ
  exact hg (himage Q hQGroup hQ q g)

/-- The two useful formulations of quotient rigidity are equivalent:
every nontrivial quotient is nonsofic exactly when every homomorphism into a
sofic group is trivial. -/
theorem everyNontrivialQuotientIsNonsofic_iff_noNontrivialSoficImage
    {J : Type} [Group J] :
    EveryNontrivialQuotientIsNonsofic J ↔ HasNoNontrivialSoficImage J :=
  ⟨hasNoNontrivialSoficImage_of_everyNontrivialQuotientIsNonsofic,
    everyNontrivialQuotientIsNonsofic_of_hasNoNontrivialSoficImage⟩

/-- A convenient group-theoretic formulation of quasisimplicity: the group
is perfect, and every proper normal subgroup is central. -/
def IsQuasisimple (J : Type) [Group J] : Prop :=
  Group.IsPerfect J ∧
    ∀ N : Subgroup J, N.Normal → N ≤ Subgroup.center J ∨ N = ⊤

/-- Every countable central extension of `H` is nonsofic.  This is the
external Kun--Thom stability input in the form consumed by the universal
central-cover argument. -/
def AllCountableCentralExtensionsAreNonsofic
    (H : Type) [Group H] : Prop :=
  ∀ (E : Type) (_ : Group E) (_ : Countable E),
    CentralExtension E H → ¬ IsSofic E

namespace CentralExtension

variable {J H Q : Type} [Group J] [Group H] [Group Q]

/-- The center of a central cover lies in its kernel when the base is
centerless.  The reverse inclusion is part of `CentralExtension`, so in this
case the kernel is exactly the center. -/
theorem center_le_ker_of_center_eq_bot (P : CentralExtension J H)
    (hcenter : Subgroup.center H = ⊥) :
    Subgroup.center J ≤ P.projection.ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  have hpz : P.projection z ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨x, rfl⟩ := P.surjective h
    have hx := congrArg P.projection (Subgroup.mem_center_iff.mp hz x)
    simpa only [map_mul] using hx
  rw [hcenter] at hpz
  exact Subgroup.mem_bot.mp hpz

/-- Descend the projection of a central extension along a surjective
quotient whose kernel is killed by that projection. -/
noncomputable def descendProjection (P : CentralExtension J H)
    (q : J →* Q) (hq : Function.Surjective q)
    (hker : q.ker ≤ P.projection.ker) : Q →* H :=
  q.liftOfSurjective hq ⟨P.projection, hker⟩

@[simp] theorem descendProjection_comp_apply (P : CentralExtension J H)
    (q : J →* Q) (hq : Function.Surjective q)
    (hker : q.ker ≤ P.projection.ker) (g : J) :
    P.descendProjection q hq hker (q g) = P.projection g := by
  simp [descendProjection]

/-- A quotient of a central cover by a central subgroup contained in the
covering kernel is again a central extension of the same base. -/
noncomputable def descendAlongSurjection (P : CentralExtension J H)
    (q : J →* Q) (hq : Function.Surjective q)
    (hker : q.ker ≤ P.projection.ker) : CentralExtension Q H where
  projection := P.descendProjection q hq hker
  surjective := by
    intro h
    obtain ⟨g, rfl⟩ := P.surjective h
    exact ⟨q g, P.descendProjection_comp_apply q hq hker g⟩
  ker_le_center := by
    intro x hx
    obtain ⟨g, rfl⟩ := hq x
    have hgker : g ∈ P.projection.ker := by
      rw [MonoidHom.mem_ker]
      have hx' := hx
      rw [MonoidHom.mem_ker] at hx'
      simpa using hx'
    have hgcenter : g ∈ Subgroup.center J := P.ker_le_center hgker
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := hq y
    have hk := congrArg q (Subgroup.mem_center_iff.mp hgcenter k)
    simpa only [map_mul] using hk

/-- A perfect central extension of a simple group is quasisimple.  If a
normal subgroup maps trivially to the simple base it is central; if it maps
onto the base, perfectness removes the residual central factor. -/
theorem isQuasisimple_of_isPerfect_of_isSimpleGroup
    (P : CentralExtension J H) [Group.IsPerfect J] [IsSimpleGroup H] :
    IsQuasisimple J := by
  refine ⟨inferInstance, ?_⟩
  intro N hN
  letI : N.Normal := hN
  letI : (N.map P.projection).Normal :=
    Subgroup.Normal.map hN P.projection P.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (N.map P.projection) inferInstance with hbot | htop
  · left
    intro g hg
    apply P.ker_le_center
    rw [MonoidHom.mem_ker]
    have hmem : P.projection g ∈ N.map P.projection :=
      ⟨g, hg, rfl⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  · right
    apply subgroup_eq_top_of_surjects_mod_central P.projection N
    · intro h
      have hmem : h ∈ N.map P.projection := htop ▸ Subgroup.mem_top h
      obtain ⟨g, hg, hgh⟩ := hmem
      exact ⟨⟨g, hg⟩, hgh⟩
    · exact P.ker_le_center

end CentralExtension

/-- If a quasisimple group's nontrivial central quotients are nonsofic, then
all of its nontrivial quotients are nonsofic: the kernel of such a quotient
cannot be the whole group, hence quasisimplicity makes it central. -/
theorem everyNontrivialQuotientIsNonsofic_of_quasisimple
    {J : Type} [Group J]
    (hqs : IsQuasisimple J)
    (hcentral : ∀ (Q : Type) (_ : Group Q) (q : J →* Q),
      Function.Surjective q → (∃ g : J, q g ≠ 1) →
        q.ker ≤ Subgroup.center J → ¬ IsSofic Q) :
    EveryNontrivialQuotientIsNonsofic J := by
  intro Q hQGroup q hsurj hnontrivial
  letI : Group Q := hQGroup
  rcases hqs.2 q.ker inferInstance with hker | htop
  · exact hcentral Q hQGroup q hsurj hnontrivial hker
  · obtain ⟨g, hg⟩ := hnontrivial
    have hmem : g ∈ q.ker := htop ▸ Subgroup.mem_top g
    exact (hg (by simpa [MonoidHom.mem_ker] using hmem)).elim

/-- **Quasisimple sofic-image rigidity.**  If all nontrivial central
quotients of a quasisimple group are nonsofic, then every homomorphism from
the group into an arbitrary sofic group is trivial.  This is the mapping
form of the Steinberg-target conclusion. -/
theorem hasNoNontrivialSoficImage_of_quasisimple
    {J : Type} [Group J]
    (hqs : IsQuasisimple J)
    (hcentral : ∀ (Q : Type) (_ : Group Q) (q : J →* Q),
      Function.Surjective q → (∃ g : J, q g ≠ 1) →
        q.ker ≤ Subgroup.center J → ¬ IsSofic Q) :
    HasNoNontrivialSoficImage J :=
  hasNoNontrivialSoficImage_of_everyNontrivialQuotientIsNonsofic
    (everyNontrivialQuotientIsNonsofic_of_quasisimple hqs hcentral)

/-- The exact abstract profile advertised for the Steinberg targets:
finite presentability, Kazhdan's property `(T)`, and total rigidity of maps
into sofic groups. -/
structure FinitelyPresentedKazhdanSoficImageRigid
    (J : Type) [Group J] : Prop where
  finitelyPresented : Group.IsFinitelyPresented J
  propertyT : HasKazhdanPropertyT.{0, 0} J
  noNontrivialSoficImage : HasNoNontrivialSoficImage J

/-- Package the three advertised conclusions once finite presentation and
property `(T)` have been supplied together with the quotient obstruction. -/
theorem finitelyPresentedKazhdanSoficImageRigid_of_quotientObstruction
    {J : Type} [Group J]
    (hfp : Group.IsFinitelyPresented J)
    (hT : HasKazhdanPropertyT.{0, 0} J)
    (hquot : EveryNontrivialQuotientIsNonsofic J) :
    FinitelyPresentedKazhdanSoficImageRigid J :=
  ⟨hfp, hT,
    hasNoNontrivialSoficImage_of_everyNontrivialQuotientIsNonsofic hquot⟩

/-- **Perfect central-cover target theorem.**  Let `J → H` be a countable
perfect central extension of a centerless simple group.  If every countable
central extension of `H` is nonsofic, then finite presentation and property
`(T)` of `J` give the full Steinberg-target profile: every map from `J` to a
sofic group is trivial.

For `J = St_n(L_{𝔽₂}(1,2))` and `H = EL_n(L_{𝔽₂}(1,2))`, the remaining
premises are precisely the classical Steinberg/Leavitt inputs. -/
theorem finitelyPresentedKazhdanSoficImageRigid_of_perfectCentralCover
    {J H : Type} [Group J] [Group H] [Countable J]
    [Group.IsPerfect J] [IsSimpleGroup H]
    (P : CentralExtension J H)
    (hcenter : Subgroup.center H = ⊥)
    (hall : AllCountableCentralExtensionsAreNonsofic H)
    (hfp : Group.IsFinitelyPresented J)
    (hT : HasKazhdanPropertyT.{0, 0} J) :
    FinitelyPresentedKazhdanSoficImageRigid J := by
  apply finitelyPresentedKazhdanSoficImageRigid_of_quotientObstruction hfp hT
  apply everyNontrivialQuotientIsNonsofic_of_quasisimple
    (P.isQuasisimple_of_isPerfect_of_isSimpleGroup)
  intro Q hQGroup q hsurj _ hqcentral
  letI : Group Q := hQGroup
  letI : Countable Q := hsurj.countable
  have hcenterker : Subgroup.center J ≤ P.projection.ker :=
    P.center_le_ker_of_center_eq_bot hcenter
  exact hall Q hQGroup inferInstance
    (P.descendAlongSurjection q hsurj (hqcentral.trans hcenterker))

/-- **Quasisimple-target Kazhdan-corner bridge.**  If every nontrivial
quotient of a nontrivial Kazhdan group is nonsofic, then one weak-MF
certificate produces a hyperlinear nonsofic group.  The produced group is
the nontrivial hyperlinear quotient extracted by the Kazhdan corner.

For the proposed Steinberg application, quasisimplicity plus the
all-central-covers theorem supplies `EveryNontrivialQuotientIsNonsofic`. -/
theorem hyperlinear_nonsofic_exists_of_kazhdan_weakMF_of_quotientObstruction
    {J : Type} [Group J] [Nontrivial J]
    (hT : HasKazhdanPropertyT.{0, 0} J)
    (hMF : IsWeakMF J)
    (hquot : EveryNontrivialQuotientIsNonsofic J) :
    ∃ (Q : Type) (_ : Group Q), IsHyperlinear Q ∧ ¬ IsSofic Q := by
  obtain ⟨Q, hQGroup, q, hsurj, hhyper, g, hg⟩ :=
    hasNontrivialHyperlinearQuotient_of_kazhdan_weakMF hT hMF
  letI : Group Q := hQGroup
  exact ⟨Q, hQGroup, hhyper, hquot Q hQGroup q hsurj ⟨g, hg⟩⟩

/-- **Quasisimple Kazhdan target, final abstract form.**  If all nontrivial
central quotients of a quasisimple Kazhdan group are nonsofic, weak MF of
that group yields a hyperlinear nonsofic group.  This is the exact logical
endpoint used by the proposed `St₅(L_{𝔽₂}(1,2))` certificate. -/
theorem hyperlinear_nonsofic_exists_of_quasisimple_kazhdan_weakMF
    {J : Type} [Group J] [Nontrivial J]
    (hT : HasKazhdanPropertyT.{0, 0} J)
    (hMF : IsWeakMF J)
    (hqs : IsQuasisimple J)
    (hcentral : ∀ (Q : Type) (_ : Group Q) (q : J →* Q),
      Function.Surjective q → (∃ g : J, q g ≠ 1) →
        q.ker ≤ Subgroup.center J → ¬ IsSofic Q) :
    ∃ (Q : Type) (_ : Group Q), IsHyperlinear Q ∧ ¬ IsSofic Q :=
  hyperlinear_nonsofic_exists_of_kazhdan_weakMF_of_quotientObstruction
    hT hMF (everyNontrivialQuotientIsNonsofic_of_quasisimple hqs hcentral)

end NonsoficGroupsExist
