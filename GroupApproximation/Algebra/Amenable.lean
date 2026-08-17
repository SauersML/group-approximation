import Mathlib.GroupTheory.Coset.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.Ultrafilter.Defs

/-!
# Amenable groups

Mathlib has no notion of amenability at all, which is why several
manuscript sentences that use only *elementary* amenability facts have to
cite the literature for the whole sentence rather than for the one deep
theorem they actually depend on.  This file supplies the definition and
the permanence properties that need no analysis, so that those sentences
can be narrowed to their genuine external input.

Amenability is taken here in the finitely-additive-measure form: a
left-invariant finitely additive probability measure defined on *all*
subsets.  That is equivalent to the invariant-mean formulation and is far
easier to manipulate without any functional analysis, which is the point
--- everything below is elementary set theory and group theory.

What is proved: finite groups are amenable, and amenability passes to
subgroups.  The subgroup argument is the classical one, transported to
sets: a right transversal splits the ambient group over the subgroup, the
induced retraction is equivariant for left multiplication by subgroup
elements, and pulling the ambient measure back along it gives an invariant
measure on the subgroup.

Directed unions are here too, and they do need a limit of measures: the
measures of a fixed set form a bounded family, an ultrafilter refining the
eventually-large filter on the index picks out a limit, and the limit
inherits every axiom because each is a pointwise identity or inequality
that passes through a limit.  Invariance is the only step with content:
for a fixed group element the measures agree *eventually*, since the
element lies in all large enough subgroups, and eventual agreement along
an ultrafilter is enough.

What remains deliberately absent: closure under extensions.  That one
needs means on functions rather than on sets, which this formulation does
not carry.
-/

namespace GroupApproximation
namespace Amenability

/-- A left-invariant finitely additive probability measure on all subsets
of a group.  Left translation is written as an image rather than a scalar
action to keep the statement free of `SMul` instance choices. -/
structure InvariantMean (G : Type*) [Group G] where
  /-- The measure of a subset. -/
  measure : Set G → ℝ
  nonneg : ∀ A, 0 ≤ measure A
  measure_univ : measure Set.univ = 1
  additive : ∀ A B : Set G, Disjoint A B →
    measure (A ∪ B) = measure A + measure B
  invariant : ∀ (g : G) (A : Set G),
    measure ((fun x ↦ g * x) '' A) = measure A

/-- A group is amenable when it carries a left-invariant finitely additive
probability measure on all of its subsets. -/
def IsAmenable (G : Type*) [Group G] : Prop := Nonempty (InvariantMean G)

/-! ## Finite groups -/

/-- Counting measure, normalized, is invariant. -/
noncomputable def finiteMean (G : Type*) [Group G] [Finite G] :
    InvariantMean G where
  measure A := (A.ncard : ℝ) / (Nat.card G : ℝ)
  nonneg A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  measure_univ := by
    have hpos : (0 : ℝ) < (Nat.card G : ℝ) := by
      have : 0 < Nat.card G := Nat.card_pos
      exact_mod_cast this
    rw [Set.ncard_univ, div_self hpos.ne']
  additive A B hAB := by
    rw [Set.ncard_union_eq hAB A.toFinite B.toFinite]
    push_cast
    rw [add_div]
  invariant g A := by
    rw [Set.ncard_image_of_injective A (mul_right_injective g)]

theorem isAmenable_of_finite (G : Type*) [Group G] [Finite G] :
    IsAmenable G := ⟨finiteMean G⟩

/-- The measure of a subset is at most the measure of a superset. -/
theorem InvariantMean.mono {G : Type*} [Group G] (m : InvariantMean G)
    {A B : Set G} (h : A ⊆ B) : m.measure A ≤ m.measure B := by
  have hd : Disjoint A (B \ A) := disjoint_sdiff_self_right
  have hsum : m.measure (A ∪ (B \ A)) = m.measure A + m.measure (B \ A) :=
    m.additive _ _ hd
  rw [Set.union_sdiff_cancel h] at hsum
  have := m.nonneg (B \ A)
  linarith

/-! ## Subgroups -/

variable {G : Type*} [Group G] (H : Subgroup G)

/-- A chosen representative of the right coset `H g`. -/
noncomputable def cosetRep (g : G) : G :=
  (Quotient.mk (QuotientGroup.rightRel H) g).out

theorem cosetRep_spec (g : G) : g * (cosetRep H g)⁻¹ ∈ H := by
  have h : Quotient.mk (QuotientGroup.rightRel H) (cosetRep H g) =
      Quotient.mk (QuotientGroup.rightRel H) g := Quotient.out_eq _
  have h2 : QuotientGroup.rightRel H (cosetRep H g) g := Quotient.exact h
  exact QuotientGroup.rightRel_apply.mp h2

theorem cosetRep_mul_left (k : H) (g : G) :
    cosetRep H ((k : G) * g) = cosetRep H g := by
  refine congrArg Quotient.out (Quotient.sound ?_)
  show QuotientGroup.rightRel H ((k : G) * g) g
  refine QuotientGroup.rightRel_apply.mpr ?_
  have hg : g * ((k : G) * g)⁻¹ = (k : G)⁻¹ := by
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hg]
  exact H.inv_mem k.2

/-- The retraction of the ambient group onto the subgroup determined by the
chosen right transversal. -/
noncomputable def retract (g : G) : H := ⟨g * (cosetRep H g)⁻¹, cosetRep_spec H g⟩

theorem retract_mul_left (k : H) (g : G) :
    retract H ((k : G) * g) = k * retract H g := by
  refine Subtype.ext ?_
  show (k : G) * g * (cosetRep H ((k : G) * g))⁻¹ =
    (k : G) * (g * (cosetRep H g)⁻¹)
  rw [cosetRep_mul_left, mul_assoc]

theorem preimage_image_retract (k : H) (A : Set H) :
    retract H ⁻¹' ((fun x ↦ k * x) '' A) =
      (fun x : G ↦ (k : G) * x) '' (retract H ⁻¹' A) := by
  ext g
  constructor
  · rintro ⟨a, ha, hka⟩
    refine ⟨(k : G)⁻¹ * g, ?_, ?_⟩
    swap
    · show (k : G) * ((k : G)⁻¹ * g) = g
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    have hret : retract H ((k : G)⁻¹ * g) = k⁻¹ * retract H g := by
      have := retract_mul_left H k⁻¹ g
      simpa using this
    rw [Set.mem_preimage, hret, ← hka]
    simpa using ha
  · rintro ⟨x, hx, rfl⟩
    refine ⟨retract H x, hx, ?_⟩
    rw [retract_mul_left]

/-- Pulling an invariant measure back along the retraction gives an
invariant measure on the subgroup. -/
noncomputable def subgroupMean (m : InvariantMean G) : InvariantMean H where
  measure A := m.measure (retract H ⁻¹' A)
  nonneg _ := m.nonneg _
  measure_univ := by
    have h : retract H ⁻¹' (Set.univ : Set H) = Set.univ := by simp
    rw [h, m.measure_univ]
  additive A B hAB := by
    rw [Set.preimage_union]
    exact m.additive _ _ (hAB.preimage _)
  invariant k A := by
    rw [preimage_image_retract, m.invariant]

/-- **Amenability passes to subgroups.** -/
theorem IsAmenable.subgroup (h : IsAmenable G) (H : Subgroup G) :
    IsAmenable H := by
  obtain ⟨m⟩ := h
  exact ⟨subgroupMean H m⟩

/-! ## Directed unions -/

section DirectedUnion

open Filter Topology

variable {ι : Type*} [Nonempty ι] [SemilatticeSup ι] {G : Type*} [Group G]

/-- An ultrafilter refining the eventually-large filter on the index. -/
noncomputable def indexUltrafilter (ι : Type*) (hι : Nonempty ι)
    [SemilatticeSup ι] : Ultrafilter ι :=
  haveI := hι
  (Ultrafilter.exists_le (Filter.atTop : Filter ι)).choose

omit [Nonempty ι] in
theorem indexUltrafilter_le (hι : Nonempty ι) :
    (indexUltrafilter ι hι : Filter ι) ≤ Filter.atTop :=
  haveI := hι
  (Ultrafilter.exists_le (Filter.atTop : Filter ι)).choose_spec

omit [Nonempty ι] [SemilatticeSup ι] in
/-- Every family of reals confined to a closed interval has a limit along
an ultrafilter. -/
theorem exists_ultrafilter_tendsto_Icc (u : Ultrafilter ι) (f : ι → ℝ)
    {a b : ℝ} (hf : ∀ i, f i ∈ Set.Icc a b) :
    ∃ L ∈ Set.Icc a b, Filter.Tendsto f u (nhds L) := by
  have hmap : ((u.map f : Ultrafilter ℝ) : Filter ℝ) ≤
      Filter.principal (Set.Icc a b) := by
    rw [Filter.le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
    exact Filter.Eventually.of_forall hf
  obtain ⟨L, hL, hle⟩ := isCompact_Icc.ultrafilter_le_nhds (u.map f) hmap
  exact ⟨L, hL, hle⟩

omit [Nonempty ι] [SemilatticeSup ι] in
/-- Every bounded family of reals has a limit along an ultrafilter. -/
theorem exists_ultrafilter_tendsto (u : Ultrafilter ι) (f : ι → ℝ)
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1) :
    ∃ L ∈ Set.Icc (0 : ℝ) 1, Filter.Tendsto f u (nhds L) :=
  exists_ultrafilter_tendsto_Icc u f hf

variable (K : ι → Subgroup G)

omit [Nonempty ι] in
/-- **Directed unions.**  A group exhausted by a directed family of
amenable subgroups is amenable.  The limit is taken along an ultrafilter
refining the eventually-large filter; invariance is the only step with
content, and it holds because a fixed element lies in all large enough
members of the family. -/
theorem isAmenable_of_directed (hι : Nonempty ι) (hmono : Monotone K)
    (hcover : ∀ g : G, ∃ i, g ∈ K i) (hamen : ∀ i, IsAmenable (K i)) :
    IsAmenable G := by
  classical
  haveI := hι
  set u := indexUltrafilter ι hι with hu
  set m : ∀ i, InvariantMean (K i) := fun i ↦ (hamen i).some with hm
  set f : Set G → ι → ℝ :=
    fun A i ↦ (m i).measure {x : K i | (x : G) ∈ A} with hf
  have hbound : ∀ (A : Set G) (i : ι), f A i ∈ Set.Icc (0 : ℝ) 1 := by
    intro A i
    refine ⟨(m i).nonneg _, ?_⟩
    have := (m i).mono (Set.subset_univ {x : K i | (x : G) ∈ A})
    rwa [(m i).measure_univ] at this
  choose L hLmem hLtend using fun A : Set G ↦
    exists_ultrafilter_tendsto u (f A) (hbound A)
  refine ⟨{ measure := L
            nonneg := fun A ↦ (hLmem A).1
            measure_univ := ?_
            additive := ?_
            invariant := ?_ }⟩
  · -- total mass one
    refine tendsto_nhds_unique (hLtend Set.univ) ?_
    have : f Set.univ = fun _ ↦ (1 : ℝ) := by
      funext i
      have : {x : K i | (x : G) ∈ (Set.univ : Set G)} = Set.univ := by
        ext x; simp
      rw [hf]
      simp only
      rw [this, (m i).measure_univ]
    rw [this]
    exact tendsto_const_nhds
  · -- finite additivity
    intro A B hAB
    refine tendsto_nhds_unique (hLtend (A ∪ B)) ?_
    have hpt : f (A ∪ B) = fun i ↦ f A i + f B i := by
      funext i
      have hsplit : {x : K i | (x : G) ∈ A ∪ B} =
          {x : K i | (x : G) ∈ A} ∪ {x : K i | (x : G) ∈ B} := by
        ext x; simp [Set.mem_union]
      have hdisj : Disjoint {x : K i | (x : G) ∈ A} {x : K i | (x : G) ∈ B} := by
        rw [Set.disjoint_left]
        intro x hxA hxB
        exact (Set.disjoint_left.mp hAB) hxA hxB
      rw [hf]
      simp only
      rw [hsplit, (m i).additive _ _ hdisj]
    rw [hpt]
    exact (hLtend A).add (hLtend B)
  · -- invariance
    intro g A
    refine tendsto_nhds_unique (hLtend ((fun x ↦ g * x) '' A)) ?_
    obtain ⟨i₀, hi₀⟩ := hcover g
    have heq : ∀ i, i₀ ≤ i → f ((fun x ↦ g * x) '' A) i = f A i := by
      intro i hi
      have hgi : g ∈ K i := hmono hi hi₀
      have himg : {x : K i | (x : G) ∈ (fun x ↦ g * x) '' A} =
          (fun y : K i ↦ (⟨g, hgi⟩ : K i) * y) '' {x : K i | (x : G) ∈ A} := by
        ext x
        constructor
        · rintro ⟨a, ha, hax⟩
          have hmem : g⁻¹ * (x : G) ∈ K i := by
            refine K i |>.mul_mem (K i |>.inv_mem hgi) x.2
          refine ⟨⟨g⁻¹ * (x : G), hmem⟩, ?_, ?_⟩
          · show (g⁻¹ * (x : G)) ∈ A
            have hax' : g * a = (x : G) := hax
            have hrw : a = g⁻¹ * (x : G) := by
              rw [← hax', ← mul_assoc, inv_mul_cancel, one_mul]
            rwa [← hrw]
          · refine Subtype.ext ?_
            show g * (g⁻¹ * (x : G)) = (x : G)
            rw [← mul_assoc, mul_inv_cancel, one_mul]
        · rintro ⟨y, hy, rfl⟩
          exact ⟨(y : G), hy, rfl⟩
      rw [hf]
      simp only
      rw [himg, (m i).invariant]
    have hev : f ((fun x ↦ g * x) '' A) =ᶠ[(u : Filter ι)] f A := by
      refine Filter.mem_of_superset (indexUltrafilter_le hι (Filter.eventually_ge_atTop i₀)) ?_
      intro i hi
      exact heq i hi
    exact (hLtend A).congr' hev.symm

/-- **Locally finite groups are amenable.**  The finitely generated
subgroups form a directed family indexed by finite subsets, each finite by
hypothesis, and every element lies in the one it generates. -/
theorem isAmenable_of_locallyFinite {G : Type*} [Group G]
    (h : ∀ S : Finset G, (Subgroup.closure (S : Set G) : Set G).Finite) :
    IsAmenable G := by
  classical
  refine isAmenable_of_directed (K := fun S : Finset G ↦ Subgroup.closure (S : Set G))
    ⟨∅⟩ ?_ ?_ ?_
  · intro S T hST
    exact Subgroup.closure_mono (Finset.coe_subset.mpr hST)
  · intro g
    exact ⟨{g}, Subgroup.subset_closure (by simp)⟩
  · intro S
    haveI : Finite (Subgroup.closure (S : Set G)) := (h S).to_subtype
    exact isAmenable_of_finite _

end DirectedUnion

end Amenability
end GroupApproximation
