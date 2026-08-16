import GroupApproximation.Sofic.IntrinsicCompressionDefect
import GroupApproximation.Sofic.Type0Transfer

/-!
# Transporting a compression datum across a group isomorphism

`non_mf_groups_exist.tex` states the obstruction theorems of `sec:conj` for an
arbitrary *countable* group, with no universe.  The analytic proofs are written
for ambient groups in `Type 0`, because the corner constructions they run are
finite-stage matrix arguments that were set up there.  `Sofic.Type0Transfer`
supplies the missing half — a countable group in any universe is isomorphic to
one in `Type 0` — but a theorem about a *conjugation datum* cannot be moved by
that alone: the datum, its defect subgroup, and the subgroup the conclusion
speaks about all have to travel along the isomorphism too.

This module is that layer.  Everything in it is elementary group theory: the
Kazhdan conjugation datum is a homomorphism together with two elements and two
equational conditions, so an isomorphism carries it to a datum on the target,
and the pointwise compression defects of the image are the images of the
pointwise compression defects.  Nothing analytic is redone, nothing is
weakened, and no hypothesis is added: countability is what the manuscript
already prints, and it is exactly what the descent consumes.

The Kazhdan source `Γ` is *not* transported.  It stays in `Type 0` because
`KazhdanCompressionCore` spells property `(T)` as `HasKazhdanPropertyT.{0, 0}`,
whose group argument is pinned to the smallest universe by that notation; the
manuscript's `Λ` is untouched by any of this.
-/

namespace GroupApproximation
namespace CompressionUniverseTransfer

open scoped commutatorElement

universe u v

section Datum

variable {Γ : Type} [Group Γ] {H : Type u} [Group H] {H₀ : Type v} [Group H₀]

/-- **The conjugation datum transports along a group isomorphism.**  Each field
is a group-theoretic equation, so each is the image of the original; property
`(T)` is a statement about `Γ` alone and is carried over unchanged. -/
def mapCore (C : KazhdanCompressionCore Γ H) (e : H ≃* H₀) :
    KazhdanCompressionCore Γ H₀ where
  iota := e.toMonoidHom.comp C.iota
  t := e C.t
  c := e C.c
  kazhdan := C.kazhdan
  compresses := by
    intro γ
    obtain ⟨δ, hδ⟩ := C.compresses γ
    refine ⟨δ, ?_⟩
    have h : e (C.t * C.iota γ * C.t⁻¹) = e (C.iota δ) := by rw [hδ]
    simpa using h
  comm_c := by
    intro γ
    simpa using (C.comm_c γ).map e

@[simp] theorem mapCore_iota (C : KazhdanCompressionCore Γ H) (e : H ≃* H₀)
    (γ : Γ) : (mapCore C e).iota γ = e (C.iota γ) := rfl

@[simp] theorem mapCore_t (C : KazhdanCompressionCore Γ H) (e : H ≃* H₀) :
    (mapCore C e).t = e C.t := rfl

@[simp] theorem mapCore_c (C : KazhdanCompressionCore Γ H) (e : H ≃* H₀) :
    (mapCore C e).c = e C.c := rfl

/-- The transported root of the transported datum is the image of the root. -/
theorem mapCore_transported (C : KazhdanCompressionCore Γ H) (e : H ≃* H₀) :
    (mapCore C e).transported = e C.transported := by
  simp [KazhdanCompressionCore.transported]

/-- Each pointwise compression defect of the transported datum is the image of
the corresponding pointwise compression defect. -/
theorem mapCore_defect (C : KazhdanCompressionCore Γ H) (e : H ≃* H₀) (γ : Γ) :
    ⁅(mapCore C e).transported, (mapCore C e).iota γ⁆ =
      e ⁅C.transported, C.iota γ⁆ := by
  rw [mapCore_transported, mapCore_iota, map_commutatorElement]

/-- **The compression defect transports.**  The image of the defect normal
closure lies in the defect normal closure of the transported datum.  This is
the direction every descent argument needs: a subgroup sitting inside the
defect upstairs lands inside the defect downstairs. -/
theorem defectNormal_map_le (C : KazhdanCompressionCore Γ H) (e : H ≃* H₀) :
    C.defectNormal.map e.toMonoidHom ≤ (mapCore C e).defectNormal := by
  haveI : (((mapCore C e).defectNormal).comap e.toMonoidHom).Normal :=
    Subgroup.Normal.comap inferInstance _
  rw [Subgroup.map_le_iff_le_comap, KazhdanCompressionCore.defectNormal]
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨γ, rfl⟩
  simp only [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.coe_coe]
  exact Subgroup.subset_normalClosure ⟨γ, (mapCore_defect C e γ).symm⟩

/-- A subgroup inside the compression defect is carried into the compression
defect of the transported datum. -/
theorem map_le_defectNormal_mapCore (C : KazhdanCompressionCore Γ H)
    (e : H ≃* H₀) {F : Subgroup H} (hF : F ≤ C.defectNormal) :
    F.map e.toMonoidHom ≤ (mapCore C e).defectNormal :=
  (Subgroup.map_mono hF).trans (defectNormal_map_le C e)

end Datum

/-! ## The intrinsic defect

`sec:conj` also states its conclusions for the *intrinsic* defect `𝔇(H,L)` --
the normal closure of `⁅g z g⁻¹, ℓ⁆` over all compressors `g`, all elements `z`
centralizing `L`, and all `ℓ ∈ L` -- which is defined from `L` alone, with no
datum.  It transports for the same reason: an isomorphism carries compressors
to compressors, centralizing elements to centralizing elements, and the
displayed commutators to the displayed commutators. -/

section IntrinsicDefect

variable {H : Type u} [Group H] {H₀ : Type v} [Group H₀]

/-- An isomorphism carries one-sided compressors to one-sided compressors. -/
theorem image_compressionSet_subset (e : H ≃* H₀) (L : Subgroup H) :
    (e : H → H₀) '' compressionSet L ⊆ compressionSet (L.map e.toMonoidHom) := by
  rintro _ ⟨s, hs, rfl⟩
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨s * y * s⁻¹, hs y hy, by simp⟩

/-- The group generated by the one-sided compressors transports. -/
theorem compressionGroup_map_le (e : H ≃* H₀) (L : Subgroup H) :
    (compressionGroup L).map e.toMonoidHom ≤
      compressionGroup (L.map e.toMonoidHom) := by
  rw [compressionGroup, Subgroup.map_closure]
  exact Subgroup.closure_mono (image_compressionSet_subset e L)

/-- Each displayed intrinsic-defect generator maps to a displayed intrinsic
defect generator of the image subgroup. -/
theorem image_compressionCentralizerDefectSet_subset (e : H ≃* H₀)
    (L : Subgroup H) :
    (e : H → H₀) '' compressionCentralizerDefectSet L ⊆
      compressionCentralizerDefectSet (L.map e.toMonoidHom) := by
  rintro _ ⟨_, ⟨g, hg, z, hz, ℓ, hℓ, rfl⟩, rfl⟩
  refine ⟨e g, ?_, e z, ?_, e ℓ, Subgroup.mem_map_of_mem _ hℓ, ?_⟩
  · exact compressionGroup_map_le e L (Subgroup.mem_map_of_mem _ hg)
  · rintro _ ⟨y, hy, rfl⟩
    simpa using (hz y hy).map e
  · simp [map_commutatorElement]

/-- **The intrinsic compression--centralizer defect transports.** -/
theorem compressionCentralizerDefect_map_le (e : H ≃* H₀) (L : Subgroup H) :
    (compressionCentralizerDefect L).map e.toMonoidHom ≤
      compressionCentralizerDefect (L.map e.toMonoidHom) := by
  haveI : ((compressionCentralizerDefect
      (L.map e.toMonoidHom)).comap e.toMonoidHom).Normal :=
    Subgroup.Normal.comap inferInstance _
  rw [Subgroup.map_le_iff_le_comap, compressionCentralizerDefect]
  refine Subgroup.normalClosure_le_normal ?_
  intro x hx
  simp only [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.coe_coe]
  exact Subgroup.subset_normalClosure
    (image_compressionCentralizerDefectSet_subset e L ⟨x, hx, rfl⟩)

end IntrinsicDefect

/-! ## Transporting the ambient subgroup

The conclusions of `sec:conj` are statements about a subgroup of the ambient
group -- that it lies in the kernel of every corona representation, or in the
MF radical.  Descent therefore has to carry the subgroup as well, together with
whichever of its finiteness, normality and property-`(T)` hypotheses the row in
question assumes. -/

section Subgroup

variable {H : Type u} [Group H] {H₀ : Type v} [Group H₀]

/-- Normality transports along an isomorphism. -/
theorem map_normal (e : H ≃* H₀) (F : Subgroup H) [F.Normal] :
    (F.map e.toMonoidHom).Normal :=
  Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective

/-- Finiteness transports along an isomorphism. -/
theorem map_finite (e : H ≃* H₀) (F : Subgroup H) [Finite F] :
    Finite (F.map e.toMonoidHom) :=
  Finite.of_equiv _
    (Subgroup.equivMapOfInjective F e.toMonoidHom e.injective).toEquiv

/-- Membership in the image, for the element the conclusion is read at. -/
theorem mem_map_of_mem (e : H ≃* H₀) {F : Subgroup H} {x : H} (hx : x ∈ F) :
    e x ∈ F.map e.toMonoidHom :=
  Subgroup.mem_map_of_mem _ hx

/-- **Pulling a kernel conclusion back.**  If the image of `F` lies in the
kernel of a homomorphism defined on the model, then `F` lies in the kernel of
its restriction along the isomorphism.  This is the last step of every descent
in `sec:conj`. -/
theorem le_ker_of_map_le_ker {K : Type*} [Group K] (e : H ≃* H₀)
    {F : Subgroup H} {rho : H₀ →* K}
    (h : F.map e.toMonoidHom ≤ rho.ker) :
    F ≤ (rho.comp e.toMonoidHom).ker := by
  intro x hx
  exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (h (mem_map_of_mem e hx)))

end Subgroup

end CompressionUniverseTransfer
end GroupApproximation
