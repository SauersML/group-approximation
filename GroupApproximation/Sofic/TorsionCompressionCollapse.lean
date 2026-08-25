import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Criterion.CompressionCentralizerDefect
import GroupApproximation.Algebra.CountableInstances

/-!
# Torsion compression collapse: the group-theoretic layer

The compression-collapse program upgrades the finite-normal compression
obstruction to a lamp-collapse mechanism: for a Kazhdan subgroup `L ≤ E`, a
one-sided compressor `s`, and a finite-order element `k` centralized by the
compressed copy `s L s⁻¹` whose `L`-conjugation orbit commutes pairwise,
every norm-corona representation of `E` is forced to identify `k` with its
entire `L`-conjugation orbit.

This file contains the unconditional group-theoretic layer of that program:

* `piConjStabilizer` — the subgroup of elements whose conjugation action on
  a marked element is invisible to a fixed homomorphism, and the
  propagation theorem: per-compressor collapse propagates to the entire
  expansion subgroup `⟨s⁻¹ L s : s⟩`.  This is the exact bookkeeping that
  turns the analytic one-orbit collapse into collapse along the fibers of
  `G/Γ → G/Γ↑`.
* `commute_map_of_collapse` — the abelianization forcing: once one
  nontrivially-moved partner of a lamp is identified with it, the images of
  same-fiber lamps commute.  This is what abelianizes the fiber lamp groups
  in the universal corona quotient.
* `actualCoronaMFResidual_eq_comap_quotient` — the reduction theorem for
  the universal MF quotient: a normal subgroup inside the literal MF
  radical reduces the radical computation to the quotient group.
* `torsionCollapseDefect` — the intrinsic torsion-collapse defect subgroup,
  with hypothesis-gated endpoints placing it inside the literal MF radical
  and computing the radical exactly when the quotient is MF.  The analytic
  collapse statement enters only as an explicit hypothesis; nothing here
  depends on unformalized analysis.
-/

namespace GroupApproximation
namespace TorsionCompressionCollapse

open scoped commutatorElement

noncomputable section

universe u v

variable {E : Type u} {Q : Type v} [Group E] [Group Q]

/- Quotients of countable groups are countable.  Proved once as
`GroupApproximation.CountableInstances.quotientCountable` and taken here with
the same `local` scope the mirrored copy had. -/
attribute [local instance] GroupApproximation.CountableInstances.quotientCountable

/-! ## The conjugation stabilizer of a marked element -/

/-- The subgroup of elements whose conjugation action on `k` is invisible
to the homomorphism `f`. -/
def piConjStabilizer (f : E →* Q) (k : E) : Subgroup E where
  carrier := {g | f (g * k * g⁻¹) = f k}
  one_mem' := by
    show f (1 * k * 1⁻¹) = f k
    rw [one_mul, inv_one, mul_one]
  mul_mem' := by
    intro g h hg hh
    have hg' : f (g * k * g⁻¹) = f k := hg
    have hh' : f (h * k * h⁻¹) = f k := hh
    show f (g * h * k * (g * h)⁻¹) = f k
    calc
      f (g * h * k * (g * h)⁻¹) = f (g * (h * k * h⁻¹) * g⁻¹) := by
        rw [show g * h * k * (g * h)⁻¹ = g * (h * k * h⁻¹) * g⁻¹ by group]
      _ = f g * f (h * k * h⁻¹) * f g⁻¹ := by rw [map_mul, map_mul]
      _ = f g * f k * f g⁻¹ := by rw [hh']
      _ = f (g * k * g⁻¹) := by rw [map_mul, map_mul]
      _ = f k := hg'
  inv_mem' := by
    intro g hg
    have hg' : f (g * k * g⁻¹) = f k := hg
    show f (g⁻¹ * k * g⁻¹⁻¹) = f k
    rw [inv_inv]
    calc
      f (g⁻¹ * k * g) = f g⁻¹ * f k * f g := by rw [map_mul, map_mul]
      _ = f g⁻¹ * f (g * k * g⁻¹) * f g := by rw [hg']
      _ = f (g⁻¹ * (g * k * g⁻¹) * g) := by
        rw [map_mul f (g⁻¹ * (g * k * g⁻¹)) g,
          map_mul f g⁻¹ (g * k * g⁻¹)]
      _ = f k := by rw [show g⁻¹ * (g * k * g⁻¹) * g = k by group]

@[simp] theorem mem_piConjStabilizer_iff {f : E →* Q} {k g : E} :
    g ∈ piConjStabilizer f k ↔ f (g * k * g⁻¹) = f k :=
  Iff.rfl

/-- Collapse of the marked commutator is exactly membership of the mover in
the conjugation stabilizer. -/
theorem map_commutator_eq_one_iff (f : E →* Q) (g k : E) :
    f ⁅g, k⁆ = 1 ↔ g ∈ piConjStabilizer f k := by
  rw [mem_piConjStabilizer_iff, commutatorElement_def, map_mul, map_inv]
  exact mul_inv_eq_one

/-- A subgroup that collapses pointwise lies in the conjugation
stabilizer. -/
theorem le_piConjStabilizer_of_collapse (f : E →* Q) (k : E)
    (L : Subgroup E) (hcollapse : ∀ γ ∈ L, f (γ * k * γ⁻¹) = f k) :
    L ≤ piConjStabilizer f k :=
  fun γ hγ ↦ hcollapse γ hγ

/-- Conjugating a stabilizer element transports it to the stabilizer of the
conjugated marked element. -/
theorem conj_mem_piConjStabilizer_conj (f : E →* Q) (k s g : E)
    (hg : g ∈ piConjStabilizer f k) :
    s⁻¹ * g * s ∈ piConjStabilizer f (s⁻¹ * k * s) := by
  have hg' : f (g * k * g⁻¹) = f k := hg
  show f ((s⁻¹ * g * s) * (s⁻¹ * k * s) * (s⁻¹ * g * s)⁻¹) =
    f (s⁻¹ * k * s)
  calc
    f ((s⁻¹ * g * s) * (s⁻¹ * k * s) * (s⁻¹ * g * s)⁻¹) =
        f (s⁻¹ * (g * k * g⁻¹) * s) := by
      rw [show (s⁻¹ * g * s) * (s⁻¹ * k * s) * (s⁻¹ * g * s)⁻¹ =
        s⁻¹ * (g * k * g⁻¹) * s by group]
    _ = f s⁻¹ * f (g * k * g⁻¹) * f s := by rw [map_mul, map_mul]
    _ = f s⁻¹ * f k * f s := by rw [hg']
    _ = f (s⁻¹ * k * s) := by rw [map_mul, map_mul]

/-! ## Propagation to the expansion subgroup -/

/-- The expansion subgroup of a family of one-sided compressors: the
subgroup generated by all the expanded copies `s⁻¹ L s`. -/
def expansionSubgroup (L : Subgroup E) (T : Set E) : Subgroup E :=
  Subgroup.closure (⋃ s ∈ T, (fun g ↦ s⁻¹ * g * s) '' (L : Set E))

/-- Every expanded copy of the base generates the expansion subgroup. -/
theorem le_expansionSubgroup_of_mem (L : Subgroup E) {T : Set E} {s : E}
    (hs : s ∈ T) {γ : E} (hγ : γ ∈ L) :
    s⁻¹ * γ * s ∈ expansionSubgroup L T := by
  apply Subgroup.subset_closure
  exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr
    ⟨hs, ⟨γ, hγ, rfl⟩⟩⟩

/-- **Expansion propagation.**  If a homomorphism collapses the transported
marked element `s k s⁻¹` along `L` for every compressor `s` in the family,
then the whole expansion subgroup stabilizes the marked element itself.
This is the group-theoretic closure step of the compression-collapse
argument: analytic collapse at each compressed basepoint globalizes to the
canonical expansion quotient. -/
theorem expansionSubgroup_le_piConjStabilizer (f : E →* Q) (k : E)
    (L : Subgroup E) (T : Set E)
    (hcollapse : ∀ s ∈ T, ∀ γ ∈ L,
      f (γ * (s * k * s⁻¹) * γ⁻¹) = f (s * k * s⁻¹)) :
    expansionSubgroup L T ≤ piConjStabilizer f k := by
  rw [expansionSubgroup, Subgroup.closure_le]
  rintro x hx
  simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe] at hx
  obtain ⟨s, hs, γ, hγ, rfl⟩ := hx
  have hmem : γ ∈ piConjStabilizer f (s * k * s⁻¹) :=
    hcollapse s hs γ hγ
  have htrans := conj_mem_piConjStabilizer_conj f (s * k * s⁻¹) s γ hmem
  rwa [show s⁻¹ * (s * k * s⁻¹) * s = k by group] at htrans

/-! ## Abelianization forcing -/

/-- **Fiber abelianization.**  If some mover `w` identifies `k` with a
partner `w k w⁻¹` that commutes with `k'`, then the images of `k` and `k'`
commute.  Applied to two lamps at one collapsed site with the partner taken
at a different site of the same fiber, this abelianizes the fiber lamp group
in every corona representation. -/
theorem commute_map_of_collapse (f : E →* Q) {k k' w : E}
    (hid : f (w * k * w⁻¹) = f k) (hcomm : Commute (w * k * w⁻¹) k') :
    Commute (f k) (f k') := by
  have h1 : f (w * k * w⁻¹) * f k' = f k' * f (w * k * w⁻¹) := by
    rw [← map_mul, ← map_mul, hcomm.eq]
  rw [hid] at h1
  exact h1

/-! ## The reduction theorem for the universal MF quotient -/

/-- **Reduction of the MF radical.**  A normal subgroup contained in the
literal MF radical reduces the radical to the quotient: the radical of `G`
is the full preimage of the radical of `G ⧸ N`.  Consequently the universal
MF quotient of `G` and of `G ⧸ N` coincide. -/
theorem actualCoronaMFResidual_eq_comap_quotient {G : Type u} [Group G]
    (N : Subgroup G) [N.Normal] (hN : N ≤ actualCoronaMFResidual G) :
    actualCoronaMFResidual G =
      (actualCoronaMFResidual (G ⧸ N)).comap (QuotientGroup.mk' N) := by
  ext x
  constructor
  · intro hx
    have hmap : (QuotientGroup.mk' N) x ∈
        actualCoronaMFResidual (G ⧸ N) :=
      map_actualCoronaMFResidual_le (QuotientGroup.mk' N) ⟨x, hx, rfl⟩
    exact Subgroup.mem_comap.mpr hmap
  · intro hx
    have hxq : ActualCoronaMFInvisible ((QuotientGroup.mk' N) x) :=
      Subgroup.mem_comap.mp hx
    intro X hX
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    intro rho
    have hker : N ≤ rho.ker := by
      intro y hy
      exact hN hy X hX rho
    have h1 := hxq X hX (QuotientGroup.lift N rho hker)
    calc
      rho x = (QuotientGroup.lift N rho hker)
          ((QuotientGroup.mk' N) x) := by
        rw [← MonoidHom.comp_apply, QuotientGroup.lift_comp_mk']
      _ = 1 := h1

/-! ## The torsion compression-collapse defect -/

/-- A finite-order element centralized by the `s`-compressed copy of `L`
whose `L`-conjugation orbit commutes pairwise.  These are exactly the
elements the analytic compression-collapse theorem identifies with their
entire `L`-orbit in every norm-corona representation, when `L` is Kazhdan
and `s` is a one-sided compressor of `L`. -/
def IsTorsionCompressionWitness (L : Subgroup E) (s : E) (k : E) : Prop :=
  (∃ m : ℕ, 0 < m ∧ k ^ m = 1) ∧
    (∀ γ ∈ L, Commute (s * γ * s⁻¹) k) ∧
    (∀ γ₁ ∈ L, ∀ γ₂ ∈ L, Commute (γ₁ * k * γ₁⁻¹) (γ₂ * k * γ₂⁻¹))

/-- The identity is always a witness; the witness class is nonempty. -/
theorem isTorsionCompressionWitness_one (L : Subgroup E) (s : E) :
    IsTorsionCompressionWitness L s 1 := by
  refine ⟨⟨1, Nat.one_pos, pow_one 1⟩, ?_, ?_⟩
  · intro γ _
    exact Commute.one_right _
  · intro γ₁ _ γ₂ _
    rw [show γ₁ * (1 : E) * γ₁⁻¹ = 1 by group,
      show γ₂ * (1 : E) * γ₂⁻¹ = 1 by group]

/-- The marked collapse commutators of all torsion compression witnesses. -/
def torsionCollapseSet (L : Subgroup E) (s : E) : Set E :=
  {x | ∃ k : E, IsTorsionCompressionWitness L s k ∧
    ∃ γ ∈ L, x = ⁅γ, k⁆}

/-- The intrinsic torsion compression-collapse defect subgroup. -/
def torsionCollapseDefect (L : Subgroup E) (s : E) : Subgroup E :=
  Subgroup.normalClosure (torsionCollapseSet L s)

instance torsionCollapseDefect_normal (L : Subgroup E) (s : E) :
    (torsionCollapseDefect L s).Normal :=
  Subgroup.normalClosure_normal

/-- Every displayed collapse commutator lies in the defect subgroup. -/
theorem commutator_mem_torsionCollapseDefect (L : Subgroup E) (s : E)
    {k γ : E} (hk : IsTorsionCompressionWitness L s k) (hγ : γ ∈ L) :
    ⁅γ, k⁆ ∈ torsionCollapseDefect L s :=
  Subgroup.subset_normalClosure ⟨k, hk, γ, hγ, rfl⟩

/-- A homomorphism collapsing every witness along `L` kills the whole
defect subgroup. -/
theorem torsionCollapseDefect_le_ker (L : Subgroup E) (s : E)
    (f : E →* Q)
    (hcollapse : ∀ k : E, IsTorsionCompressionWitness L s k →
      ∀ γ ∈ L, f (γ * k * γ⁻¹) = f k) :
    torsionCollapseDefect L s ≤ f.ker := by
  rw [torsionCollapseDefect]
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨k, hk, γ, hγ, rfl⟩
  show f ⁅γ, k⁆ = 1
  rw [map_commutator_eq_one_iff]
  exact hcollapse k hk γ hγ

/-- **Conditional radical membership.**  If every norm-corona
representation collapses every torsion compression witness along `L` — the
conclusion of the analytic compression-collapse theorem for a Kazhdan `L`
and a one-sided compressor `s` — then the entire torsion-collapse defect
lies in the literal MF radical.  For the involutive witness subclass the
collapse hypothesis is discharged unconditionally in
`Sofic/InvolutionCollapseEndpoint`
(`involutiveCollapseDefect_le_actualCoronaMFResidual`). -/
theorem torsionCollapseDefect_le_actualCoronaMFResidual
    (L : Subgroup E) (s : E)
    (hkill : ∀ x ∈ torsionCollapseSet L s, ActualCoronaMFInvisible x) :
    torsionCollapseDefect L s ≤ actualCoronaMFResidual E := by
  rw [torsionCollapseDefect]
  apply Subgroup.normalClosure_le_normal
  intro x hx
  exact hkill x hx

/-- **Conditional exact MF radical.**  Collapse of every witness in every
corona representation, together with the MF property of the defect
quotient, computes the literal MF radical exactly.  This is the reduction
theorem specialized to the torsion-collapse defect: the universal MF
quotient of `E` is exactly `E ⧸ torsionCollapseDefect L s`.  The
involutive-witness analogue is unconditional on the collapse side:
`Sofic/InvolutionCollapseEndpoint`. -/
theorem actualCoronaMFResidual_eq_torsionCollapseDefect
    [Countable E] (L : Subgroup E) (s : E)
    (hkill : ∀ x ∈ torsionCollapseSet L s, ActualCoronaMFInvisible x)
    (hquot : IsCDEOperatorMF (E ⧸ torsionCollapseDefect L s)) :
    actualCoronaMFResidual E = torsionCollapseDefect L s :=
  actualCoronaMFResidual_eq_of_le_and_quotient_isCDEOperatorMF
    (torsionCollapseDefect L s)
    (torsionCollapseDefect_le_actualCoronaMFResidual L s hkill) hquot

end

end TorsionCompressionCollapse
end GroupApproximation
