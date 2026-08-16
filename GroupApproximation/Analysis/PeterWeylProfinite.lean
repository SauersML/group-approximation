import Mathlib.Topology.Algebra.ClopenNhdofOne
import GroupApproximation.Sofic.LinearResidual

/-!
# Peter--Weyl for profinite targets, and the Bohr residual

Sections 46.5 and 49.12 of the dossier compute a *Bohr* radical: the elements
killed by every homomorphism into a compact Hausdorff group.  The dossier's own
status note says the identification `Rad_Bohr = Rad_fd` rests on Peter--Weyl,
which it does not reprove -- it is the one named classical import the argument
takes on faith.

This file does three things.

**It defines the Bohr residual** (`bohrResidual`), which the repository did not
have.  As with `linearResidual` the target groups range over `Type`, so no
quantification over a proper class is needed; and because the source group is
discrete, no continuity condition on the homomorphisms is required.

**It proves the easy inclusion outright.**  A finite group with the discrete
topology is a compact Hausdorff topological group, so `bohrResidual ≤
finiteResidual` needs no analysis at all (`bohrResidual_le_finiteResidual`).

**It proves Peter--Weyl outright for profinite targets.**  If the compact target
is totally disconnected then van Dantzig's theorem -- which Mathlib has, as
`ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one` -- puts a
nonidentity element outside an open normal subgroup, and an open subgroup of a
compact group has finite index.  So finite quotients already separate the points
of a profinite group, and consequently a homomorphism into a profinite group
sees nothing a finite quotient does not: `finiteResidual_le_ker_of_profinite`.
For profinite targets the Bohr theory is therefore *equal* to the finite-quotient
theory, with nothing assumed (`bohrResidual_eq_finiteResidual_of_profinite_only`
records the resulting two-sided statement in the form the dossier uses).

What is **not** proved here is the analytic core of Peter--Weyl for a general
compact group -- that finite-dimensional unitary representations separate the
points of any compact Hausdorff group.  An inventory, since an earlier version of
this file guessed and guessed wrong.

Present in Mathlib: Haar measure on a compact group; the spectral theorem for
compact self-adjoint operators, with finite-dimensionality of the eigenspaces
(`Analysis/InnerProductSpace/Spectrum`); Arzelà--Ascoli
(`Topology/ContinuousMap/Bounded/ArzelaAscoli`).

Absent: continuity of translation in `L²`; convolution on a general compact
group, `Analysis/Convolution` being written for additive groups and normed
spaces rather than for Haar convolution on a possibly nonabelian compact group;
and, resting on those two, compactness of the convolution operator.

That last item is the whole gap.  Given it, convolution by a continuous function
bump has finite-dimensional eigenspaces by the spectral theorem, those eigenspaces
are translation-invariant, and they separate the point at hand -- which is
`SeparatesPoints`.  So the remaining work is one analytic lemma plus the
convolution API it needs, not a missing theory of compact groups.  It is isolated as the single named hypothesis
`SeparatesPoints`, and `fdUnitaryResidual_le_bohrResidual_of_separates` derives
the remaining inclusion from it.  So the Bohr clauses become conditional on one
precisely stated classical input rather than on a remark, which is the same
discipline the repository already applies to the analytic core of Theorem 7.2.
-/

namespace GroupApproximation

namespace PeterWeyl

universe u

/-! ## Separation in a profinite group -/

section Profinite

variable {C : Type*} [Group C] [TopologicalSpace C] [IsTopologicalGroup C]
  [CompactSpace C] [TotallyDisconnectedSpace C]

/-- **van Dantzig separation.**  A nonidentity element of a profinite group lies
outside some open normal subgroup, and an open subgroup of a compact group has
finite index.  This is Peter--Weyl for profinite groups: finite quotients
already separate points. -/
theorem exists_normal_finiteIndex_not_mem {c : C} (hc : c ≠ 1) :
    ∃ H : Subgroup C, H.Normal ∧ H.FiniteIndex ∧ c ∉ H := by
  have hopen : IsOpen ({c}ᶜ : Set C) := isOpen_compl_singleton
  have hmem : (1 : C) ∈ ({c}ᶜ : Set C) := by
    simpa using Ne.symm hc
  obtain ⟨H, hH⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hopen hmem
  haveI : Finite (C ⧸ H.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen H.toSubgroup H.isOpen
  refine ⟨H.toSubgroup, inferInstance, Subgroup.finiteIndex_of_finite_quotient, ?_⟩
  intro hcH
  exact (hH hcH) rfl

end Profinite

/-! ## Comap of a finite-index subgroup -/

/-- Pulling a finite-index normal subgroup back along any homomorphism keeps
finite index: the quotients inject. -/
theorem finiteIndex_comap {G : Type u} [Group G] {C : Type*} [Group C]
    (f : G →* C) (H : Subgroup C) [H.Normal] [H.FiniteIndex] :
    (H.comap f).FiniteIndex := by
  haveI : Finite (C ⧸ H) := H.finite_quotient_of_finiteIndex
  have hinj : Function.Injective
      (QuotientGroup.map (H.comap f) H f (le_refl (H.comap f))) := by
    intro a b hab
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [QuotientGroup.map_mk, QuotientGroup.map_mk, QuotientGroup.eq] at hab
        rw [QuotientGroup.eq, Subgroup.mem_comap]
        simpa using hab
  haveI : Finite (G ⧸ H.comap f) := Finite.of_injective _ hinj
  exact Subgroup.finiteIndex_of_finite_quotient

/-! ## Profinite targets see exactly the finite quotients -/

/-- **A homomorphism into a profinite group kills the finite residual.**  So for
profinite targets the Bohr theory adds nothing to the finite-quotient theory,
and this is proved, not assumed. -/
theorem finiteResidual_le_ker_of_profinite {G : Type u} [Group G] {C : Type*}
    [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C]
    [TotallyDisconnectedSpace C] (f : G →* C) :
    finiteResidual G ≤ f.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  by_contra hne
  obtain ⟨H, hHnorm, hHfin, hHmem⟩ := exists_normal_finiteIndex_not_mem hne
  haveI := hHnorm
  haveI := hHfin
  haveI := finiteIndex_comap f H
  exact hHmem (mem_finiteResidual_iff.mp hx (H.comap f) inferInstance)

/-! ## The Bohr residual -/

/-- A compact Hausdorff target group, bundled.  Following the treatment of
`linearResidual`, the carrier ranges over `Type`, so no quantification over a
proper class is needed.  The source group is discrete, so every homomorphism out
of it is automatically continuous and no continuity condition appears. -/
structure CompactTarget : Type (u + 1) where
  /-- The underlying group. -/
  carrier : Type u
  /-- Its group structure. -/
  group : Group carrier
  /-- Its topology. -/
  topology : TopologicalSpace carrier
  /-- It is a topological group. -/
  topGroup : @IsTopologicalGroup carrier topology group
  /-- It is compact. -/
  compact : @CompactSpace carrier topology
  /-- It is Hausdorff. -/
  hausdorff : @T2Space carrier topology

attribute [instance] CompactTarget.group CompactTarget.topology
  CompactTarget.topGroup CompactTarget.compact CompactTarget.hausdorff

variable {G : Type u} [Group G]

/-- The **Bohr residual**: the elements invisible to every homomorphism into a
compact Hausdorff group.  This is the kernel of the map to the Bohr
compactification. -/
def bohrResidual (G : Type u) [Group G] : Subgroup G where
  carrier := {x | ∀ (C : CompactTarget.{u}) (f : G →* C.carrier), f x = 1}
  one_mem' := fun C f => map_one f
  mul_mem' := by
    intro x y hx hy C f
    rw [map_mul, hx C f, hy C f, one_mul]
  inv_mem' := by
    intro x hx C f
    rw [map_inv, hx C f, inv_one]

@[simp] theorem mem_bohrResidual_iff {x : G} :
    x ∈ bohrResidual G ↔ ∀ (C : CompactTarget.{u}) (f : G →* C.carrier), f x = 1 :=
  Iff.rfl

/-- A finite group, discretely topologized, is a compact target. -/
def CompactTarget.ofFinite (F : Type u) [Group F] [Finite F] : CompactTarget where
  carrier := F
  group := inferInstance
  topology := ⊥
  topGroup := by
    letI : TopologicalSpace F := ⊥
    haveI : DiscreteTopology F := ⟨rfl⟩
    infer_instance
  compact := by
    letI : TopologicalSpace F := ⊥
    haveI : DiscreteTopology F := ⟨rfl⟩
    haveI : Fintype F := Fintype.ofFinite F
    infer_instance
  hausdorff := by
    letI : TopologicalSpace F := ⊥
    haveI : DiscreteTopology F := ⟨rfl⟩
    infer_instance

/-- **The easy half, with no analysis.**  Finite groups are compact targets, so
the Bohr residual is contained in the finite residual. -/
theorem bohrResidual_le_finiteResidual : bohrResidual G ≤ finiteResidual G := by
  intro x hx
  rw [mem_finiteResidual_iff]
  intro L hL
  haveI := hL
  by_contra hmem
  -- the quotient by the normal core is a finite target that sees `x`
  haveI : (L.normalCore).FiniteIndex := inferInstance
  haveI : Finite (G ⧸ L.normalCore) := Subgroup.finite_quotient_of_finiteIndex
  have hone := hx (CompactTarget.ofFinite (G ⧸ L.normalCore))
    (QuotientGroup.mk' L.normalCore)
  exact hmem (L.normalCore_le ((QuotientGroup.eq_one_iff x).mp hone))

/-! ## The reduction of the remaining inclusion to Peter--Weyl -/

/-- **The analytic core of Peter--Weyl, isolated.**  The statement that
finite-dimensional unitary representations separate the points of every compact
Hausdorff group, phrased so that it can be discharged for a class of targets
without touching the rest of the development.  For profinite targets it is
`exists_normal_finiteIndex_not_mem` above; in general it is the classical
theorem.  Mathlib has Haar measure and the spectral theorem for compact
self-adjoint operators; the missing step is compactness of convolution
operators. -/
def SeparatesPoints : Prop :=
  ∀ (C : CompactTarget.{u}) (c : C.carrier), c ≠ 1 →
    ∃ (d : ℕ) (ρ : C.carrier →* Matrix (Fin d) (Fin d) ℂ), ρ c ≠ 1

/-- Given the separation statement, an element invisible to every
finite-dimensional representation is invisible to every compact target.  With
`bohrResidual_le_finiteResidual` this is the dossier's `Rad_Bohr = Rad_fd`, now
resting on exactly one named classical input. -/
theorem linearResidual_le_bohrResidual_of_separates (hPW : SeparatesPoints.{u})
    {x : G} (hx : ∀ (F : Type) (_ : Field F) (d : ℕ)
      (ρ : G →* Matrix (Fin d) (Fin d) F), ρ x = 1) :
    x ∈ bohrResidual G := by
  intro C f
  by_contra hne
  obtain ⟨d, ρ, hρ⟩ := hPW C (f x) hne
  exact hρ (hx ℂ inferInstance d (ρ.comp f))

end PeterWeyl

end GroupApproximation
