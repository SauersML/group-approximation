import GroupApproximation.Sofic.FullMFRadicalQuotientLattice

/-!
# Localization of the universal MF-visible quotient

Every homomorphism induces a map between the quotients by the genuine
norm-matrix-corona residual.  If the homomorphism is surjective and its
kernel is already invisible in the source, the induced map is an
isomorphism.  Thus the universal MF-visible quotient is unchanged by
discarding an MF-invisible kernel.
-/

namespace GroupApproximation

noncomputable section

universe u v w

variable {G : Type u} [Group G] {H : Type v} [Group H]
  {K : Type w} [Group K]

/-- The map on universal MF-visible quotients induced by a homomorphism. -/
def actualCoronaMFVisibleQuotientMap (f : G →* H) :
    G ⧸ actualCoronaMFResidual G →*
      H ⧸ actualCoronaMFResidual H :=
  QuotientGroup.map (actualCoronaMFResidual G)
    (actualCoronaMFResidual H) f (map_actualCoronaMFResidual_le f)

@[simp]
theorem actualCoronaMFVisibleQuotientMap_mk
    (f : G →* H) (x : G) :
    actualCoronaMFVisibleQuotientMap f
        (QuotientGroup.mk' (actualCoronaMFResidual G) x) =
      QuotientGroup.mk' (actualCoronaMFResidual H) (f x) :=
  rfl

/-- The induced maps on universal MF-visible quotients respect
composition. -/
theorem actualCoronaMFVisibleQuotientMap_comp
    (f : G →* H) (g : H →* K) :
    actualCoronaMFVisibleQuotientMap (g.comp f) =
      (actualCoronaMFVisibleQuotientMap g).comp
        (actualCoronaMFVisibleQuotientMap f) := by
  ext z
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (actualCoronaMFResidual G) z
  rfl

/-- A surjection with MF-invisible kernel induces a bijection on the
universal MF-visible quotients. -/
theorem actualCoronaMFVisibleQuotientMap_bijective_of_invisibleKernel
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ actualCoronaMFResidual G) :
    Function.Bijective (actualCoronaMFVisibleQuotientMap f) := by
  have hpull :=
    actualCoronaMFResidual_eq_comap_of_surjective_of_ker_le
      f hf hker
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ :=
      QuotientGroup.mk'_surjective (actualCoronaMFResidual G) a
    obtain ⟨y, rfl⟩ :=
      QuotientGroup.mk'_surjective (actualCoronaMFResidual G) b
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hfy : f x / f y ∈ actualCoronaMFResidual H :=
      QuotientGroup.eq_iff_div_mem.mp hab
    have hxy : x / y ∈ (actualCoronaMFResidual H).comap f := by
      rw [Subgroup.mem_comap]
      simpa using hfy
    rwa [← hpull] at hxy
  · intro z
    obtain ⟨h, rfl⟩ :=
      QuotientGroup.mk'_surjective (actualCoronaMFResidual H) z
    obtain ⟨g, rfl⟩ := hf h
    exact ⟨QuotientGroup.mk' (actualCoronaMFResidual G) g, rfl⟩

/-- The canonical isomorphism of universal MF-visible quotients induced by
a surjection with MF-invisible kernel. -/
def actualCoronaMFVisibleQuotientEquivOfInvisibleKernel
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ actualCoronaMFResidual G) :
    (G ⧸ actualCoronaMFResidual G) ≃*
      (H ⧸ actualCoronaMFResidual H) :=
  MulEquiv.ofBijective (actualCoronaMFVisibleQuotientMap f)
    (actualCoronaMFVisibleQuotientMap_bijective_of_invisibleKernel
      f hf hker)

end

end GroupApproximation
