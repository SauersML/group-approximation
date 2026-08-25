import GroupApproximation.Sofic.FullMFRadicalClosurePullback

/-!
# The ordered family of MF quotients

A normal subgroup is an MF quotient kernel when it is fixed by the
finite-matrix-kernel closure.  A surjection whose kernel is already contained
in the source MF residual preserves the entire ordered family of these
kernels: image and inverse image are mutually inverse order isomorphisms.
-/

namespace GroupApproximation

noncomputable section

universe u v

/-- A normal subgroup whose quotient contains no further universally forced
MF relations.  For countable groups these are exactly the kernels with MF
quotient. -/
structure MFClosedNormalSubgroup (G : Type u) [Group G] where
  carrier : Subgroup G
  normal : carrier.Normal
  closed : @actualCoronaMFClosure G _ carrier normal = carrier

namespace MFClosedNormalSubgroup

variable {G : Type u} [Group G] {H : Type v} [Group H]

instance (N : MFClosedNormalSubgroup G) : N.carrier.Normal :=
  N.normal

instance : LE (MFClosedNormalSubgroup G) :=
  ⟨fun N M ↦ N.carrier ≤ M.carrier⟩

@[ext]
theorem ext {N M : MFClosedNormalSubgroup G}
    (h : N.carrier = M.carrier) : N = M := by
  cases N
  cases M
  cases h
  rfl

instance : PartialOrder (MFClosedNormalSubgroup G) where
  le_refl N := by
    change N.carrier ≤ N.carrier
    exact le_rfl
  le_trans N M P hNM hMP := by
    change N.carrier ≤ P.carrier
    exact hNM.trans hMP
  le_antisymm N M hNM hMN := ext (le_antisymm hNM hMN)

/-- The image of an MF quotient kernel across an invisible-kernel
surjection. -/
def mapOfInvisibleKernel (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ actualCoronaMFResidual G)
    (N : MFClosedNormalSubgroup G) : MFClosedNormalSubgroup H := by
  letI : (N.carrier.map f).Normal :=
    Subgroup.Normal.map N.normal f hf
  refine
    { carrier := N.carrier.map f
      normal := inferInstance
      closed := ?_ }
  have hclosed :=
    (actualCoronaMFClosure_eq_self_iff_map_of_surjective_of_ker_le
      f hf hker N.carrier).mp N.closed
  exact hclosed.2

/-- The inverse image of an MF quotient kernel across an invisible-kernel
surjection. -/
def comapOfInvisibleKernel (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ actualCoronaMFResidual G)
    (M : MFClosedNormalSubgroup H) : MFClosedNormalSubgroup G := by
  letI : (M.carrier.comap f).Normal := M.normal.comap f
  refine
    { carrier := M.carrier.comap f
      normal := inferInstance
      closed := ?_ }
  have hpull :=
    actualCoronaMFClosure_eq_comap_map_of_surjective_of_ker_le
      f hf hker (M.carrier.comap f)
  simpa only [Subgroup.map_comap_eq_self_of_surjective hf, M.closed]
    using hpull

@[simp]
theorem mapOfInvisibleKernel_carrier (f : G →* H)
    (hf : Function.Surjective f)
    (hker : f.ker ≤ actualCoronaMFResidual G)
    (N : MFClosedNormalSubgroup G) :
    (mapOfInvisibleKernel f hf hker N).carrier = N.carrier.map f :=
  by
    unfold mapOfInvisibleKernel
    rfl

@[simp]
theorem comapOfInvisibleKernel_carrier (f : G →* H)
    (hf : Function.Surjective f)
    (hker : f.ker ≤ actualCoronaMFResidual G)
    (M : MFClosedNormalSubgroup H) :
    (comapOfInvisibleKernel f hf hker M).carrier = M.carrier.comap f :=
  by
    unfold comapOfInvisibleKernel
    rfl

/-- Image and inverse image give an order isomorphism between all MF quotient
kernels of the source and target. -/
def orderIsoOfInvisibleKernel (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ actualCoronaMFResidual G) :
    MFClosedNormalSubgroup G ≃o MFClosedNormalSubgroup H where
  toFun := mapOfInvisibleKernel f hf hker
  invFun := comapOfInvisibleKernel f hf hker
  left_inv N := by
    apply ext
    rw [comapOfInvisibleKernel_carrier, mapOfInvisibleKernel_carrier]
    have hkN :=
      ((actualCoronaMFClosure_eq_self_iff_map_of_surjective_of_ker_le
        f hf hker N.carrier).mp N.closed).1
    exact Subgroup.comap_map_eq_self hkN
  right_inv M := by
    apply ext
    rw [mapOfInvisibleKernel_carrier, comapOfInvisibleKernel_carrier]
    exact Subgroup.map_comap_eq_self_of_surjective hf M.carrier
  map_rel_iff' := by
    intro N M
    change N.carrier.map f ≤ M.carrier.map f ↔ N.carrier ≤ M.carrier
    constructor
    · intro h
      have hc := Subgroup.comap_mono (f := f) h
      have hkN :=
        ((actualCoronaMFClosure_eq_self_iff_map_of_surjective_of_ker_le
          f hf hker N.carrier).mp N.closed).1
      have hkM :=
        ((actualCoronaMFClosure_eq_self_iff_map_of_surjective_of_ker_le
          f hf hker M.carrier).mp M.closed).1
      rwa [Subgroup.comap_map_eq_self hkN,
        Subgroup.comap_map_eq_self hkM] at hc
    · exact Subgroup.map_mono

/-- The correspondence preserves and reflects every inclusion between MF
quotient kernels. -/
theorem map_le_map_iff_of_invisibleKernel
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ actualCoronaMFResidual G)
    (N M : MFClosedNormalSubgroup G) :
    N.carrier.map f ≤ M.carrier.map f ↔ N.carrier ≤ M.carrier :=
  (orderIsoOfInvisibleKernel f hf hker).le_iff_le

end MFClosedNormalSubgroup

universe w

variable {G : Type u} [Group G] {H : Type v} [Group H]
  {K : Type w} [Group K]

/-- Surjections with MF-invisible kernel are closed under composition. -/
theorem ker_comp_le_actualCoronaMFResidual
    (f : G →* H) (g : H →* K)
    (hf : Function.Surjective f)
    (hkerF : f.ker ≤ actualCoronaMFResidual G)
    (hkerG : g.ker ≤ actualCoronaMFResidual H) :
    (g.comp f).ker ≤ actualCoronaMFResidual G := by
  have hpull :=
    actualCoronaMFResidual_eq_comap_of_surjective_of_ker_le
      f hf hkerF
  intro x hx
  rw [hpull, Subgroup.mem_comap]
  apply hkerG
  rw [MonoidHom.mem_ker]
  exact MonoidHom.mem_ker.mp hx

/-- The composite of two surjective group homomorphisms is surjective as a
group homomorphism. -/
theorem surjective_monoidHom_comp
    (f : G →* H) (g : H →* K)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (g.comp f) := by
  intro z
  obtain ⟨y, rfl⟩ := hg z
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨x, rfl⟩

/-- The image correspondence on MF quotient kernels respects composition. -/
theorem MFClosedNormalSubgroup.mapOfInvisibleKernel_comp
    (f : G →* H) (g : H →* K)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hkerF : f.ker ≤ actualCoronaMFResidual G)
    (hkerG : g.ker ≤ actualCoronaMFResidual H)
    (N : MFClosedNormalSubgroup G) :
    MFClosedNormalSubgroup.mapOfInvisibleKernel
        (g.comp f) (surjective_monoidHom_comp f g hf hg)
        (ker_comp_le_actualCoronaMFResidual f g hf hkerF hkerG) =
      MFClosedNormalSubgroup.mapOfInvisibleKernel g hg hkerG
        (MFClosedNormalSubgroup.mapOfInvisibleKernel f hf hkerF N) := by
  apply MFClosedNormalSubgroup.ext
  simp only [MFClosedNormalSubgroup.mapOfInvisibleKernel_carrier]
  rw [Subgroup.map_map]

end

end GroupApproximation
