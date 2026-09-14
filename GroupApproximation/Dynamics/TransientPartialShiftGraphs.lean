import GroupApproximation.Dynamics.TransientCellsClosed
import GroupApproximation.Dynamics.ChainRecurrentPeriodic
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:transient-matrices`: partial shift graphs, their sources and ranges, and unique arrows

`non_mf_groups_exist.tex`, the proof of Lemma `lem:transient-matrices` (tex 1487–1493 at origin/main
`68481e4d7`):

> Express a prescribed finite subset of $I$ as linear combinations of characteristic functions of
> compact clopen partial shift graphs.  Include inverse partial shifts, and let $C$ be the union of
> their sources and ranges.  [...]  Freeness on $U$ makes the arrow between related points unique.

* `eq_sum_partialShiftGraphs`: every `x ∈ R_X` is `∑_g ∑_c c · 1_{D_{g,c}} u^g`, where `D_{g,c}` is
  the fiber of the Laurent coefficient of `u^g` at the value `c ≠ 0`.  For `x ∈ I` the domains are
  compact clopen and miss `Y = CR(T)` (`printedPartialShiftGraphExpansion`).
* `sourceRangeUnion T k F`: the union of the sources `D` and ranges `T^{-g}(D)` of these graphs
  together with those of the inverse graphs `(T^{-g}(D), g⁻¹)`.  It is clopen, compact, misses `Y`
  and carries every coefficient of `F` (`printedSourceRangeUnion`).
* `exists_transientCells_sourceRangeUnion`: the cells of the lemma over this `C`, so
  `transientCellsStatement_sourceRangeUnion` and
  `transientIdealLocallyMatricialStatement_sourceRangeUnion` are closed with `C` as printed.
* `Dynamics.eq_of_zpow_apply_eq_of_not_mem_chainRecurrentSet`: a point off `CR(T)` has no periodic
  orbit, so `T^d x = T^{d'} x` forces `d = d'` (`printedFreenessUniqueArrow`).
-/

namespace GroupApproximation

namespace Dynamics

section Freeness

variable {X : Type*} [UniformSpace X]

theorem homeomorph_pow_apply_eq_iterate (T : X ≃ₜ X) (n : ℕ) (x : X) : (T ^ n) x = T^[n] x := by
  induction n with
  | zero => rw [pow_zero, Homeomorph.one_apply, Function.iterate_zero, id_eq]
  | succ n ih => rw [pow_succ', Homeomorph.mul_apply, ih, Function.iterate_succ_apply']

/-- **Freeness on `U = X ∖ CR(T)`**: a point off the chain-recurrent set is not periodic, so the
exponent of an arrow between two points of its orbit is unique. -/
theorem eq_of_zpow_apply_eq_of_not_mem_chainRecurrentSet (T : X ≃ₜ X) {x : X}
    (hx : x ∉ chainRecurrentSet ⇑T) {d d' : ℤ} (h : (T ^ d) x = (T ^ d') x) : d = d' := by
  obtain ⟨e, he⟩ : ∃ e : ℤ, e = -d' + d := ⟨_, rfl⟩
  have hfix : (T ^ e) x = x := by
    rw [he, ← zpow_apply_zpow_apply, h, zpow_apply_zpow_apply, neg_add_cancel, zpow_zero,
      Homeomorph.one_apply]
  by_contra hne
  have he0 : e ≠ 0 := by omega
  have hpos : 0 < e.natAbs := Int.natAbs_pos.2 he0
  have hper : Function.IsPeriodicPt ⇑T e.natAbs x := by
    show (⇑T)^[e.natAbs] x = x
    rw [← homeomorph_pow_apply_eq_iterate, ← zpow_natCast]
    rcases Int.natAbs_eq e with hn | hn
    · rw [← hn]
      exact hfix
    · have hn' : (e.natAbs : ℤ) = -e := (neg_eq_iff_eq_neg.2 hn).symm
      rw [hn']
      calc (T ^ (-e)) x = (T ^ (-e)) ((T ^ e) x) := by rw [hfix]
        _ = x := by rw [zpow_apply_zpow_apply, neg_add_cancel, zpow_zero, Homeomorph.one_apply]
  exact hx (isChainRecurrent_of_isPeriodicPt hpos hper)

end Freeness

/-- **Printed (tex 1492–1493).**  "Freeness on $U$ makes the arrow between related points unique":
for `x ∉ CR(T)`, `T^d x = T^{d'} x` forces `d = d'`. -/
def PrintedFreenessUniqueArrow : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X) (x : X),
    x ∉ chainRecurrentSet ⇑T → ∀ d d' : ℤ, (T ^ d) x = (T ^ d') x → d = d'

theorem printedFreenessUniqueArrow : PrintedFreenessUniqueArrow :=
  fun _ _ _ _ T _ hx _ _ h => eq_of_zpow_apply_eq_of_not_mem_chainRecurrentSet T hx h

end Dynamics

namespace ClopenCrossedProduct

open ChainCore
open Multiplicative (ofAdd toAdd)

/-! ## Partial shift graphs -/

section Graphs

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type*) [Ring k]

/-- The Laurent coefficient of `x` at `u^g`, as a locally constant function. -/
noncomputable def coeffFn (x : ClopenCrossedProduct T k) (g : Multiplicative ℤ) :
    LocallyConstant X k :=
  (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g)

/-- The domain of the partial shift graph of `u^g` with coefficient value `c`. -/
def graphDomain (x : ClopenCrossedProduct T k) (g : Multiplicative ℤ) (c : k) : Set X :=
  {z | coeffFn T k x g z = c}

theorem isClopen_graphDomain (x : ClopenCrossedProduct T k) (g : Multiplicative ℤ) (c : k) :
    IsClopen (graphDomain T k x g c) :=
  (coeffFn T k x g).isLocallyConstant.isClopen_fiber c

open Classical in
/-- The nonzero values of the coefficient of `u^g`. -/
noncomputable def graphValues [CompactSpace X] (x : ClopenCrossedProduct T k)
    (g : Multiplicative ℤ) : Finset k :=
  (coeffFn T k x g).range_finite.toFinset.erase 0

theorem mem_graphValues [CompactSpace X] {x : ClopenCrossedProduct T k} {g : Multiplicative ℤ}
    {c : k} : c ∈ graphValues T k x g ↔ c ≠ 0 ∧ c ∈ Set.range (coeffFn T k x g) := by
  classical
  unfold graphValues
  rw [Finset.mem_erase, Set.Finite.mem_toFinset]

/-- A locally constant function is the combination of the indicators of its nonzero fibers. -/
theorem sum_smul_charFn_graphDomain [CompactSpace X] (x : ClopenCrossedProduct T k)
    (g : Multiplicative ℤ) :
    ∑ c ∈ graphValues T k x g, c • LocallyConstant.charFn k (isClopen_graphDomain T k x g c) =
      coeffFn T k x g := by
  ext z
  rw [← LocallyConstant.evalRingHom_apply z, map_sum]
  simp only [LocallyConstant.evalRingHom_apply, LocallyConstant.smul_apply,
    LocallyConstant.coe_charFn, smul_eq_mul]
  rw [Finset.sum_eq_single (coeffFn T k x g z)]
  · rw [Set.indicator_of_mem (show z ∈ graphDomain T k x g (coeffFn T k x g z) from rfl),
      Pi.one_apply, mul_one]
  · intro b _ hb
    rw [Set.indicator_of_notMem (show z ∉ graphDomain T k x g b from fun h => hb h.symm), mul_zero]
  · intro h
    have h0 : coeffFn T k x g z = 0 := by
      by_contra hne
      exact h ((mem_graphValues T k).2 ⟨hne, z, rfl⟩)
    rw [h0, zero_mul]

/-- The partial shift `f u^g` is the monomial `single g f`. -/
theorem coeff_mul_unit_zpow_toAdd (f : LocallyConstant X k) (g : Multiplicative ℤ) :
    coeff T k f * ↑(unit T k ^ toAdd g) = SkewMonoidAlgebra.single g (ClopenCoeff.of T k f) := by
  rw [Pestov91.CrossedProduct.val_unit_zpow, coeff_apply, Pestov91.CrossedProduct.C_mul_single,
    mul_one, ofAdd_toAdd]

/-- **The expansion into partial shift graphs** (tex 1487–1489): `x = ∑_g ∑_c c · 1_{D_{g,c}} u^g`. -/
theorem eq_sum_partialShiftGraphs [CompactSpace X] (x : ClopenCrossedProduct T k) :
    x = ∑ g ∈ SkewMonoidAlgebra.support x, ∑ c ∈ graphValues T k x g,
      coeff T k (c • LocallyConstant.charFn k (isClopen_graphDomain T k x g c)) *
        ↑(unit T k ^ toAdd g) := by
  have hx : ∑ g ∈ SkewMonoidAlgebra.support x,
      SkewMonoidAlgebra.single g (SkewMonoidAlgebra.coeff x g) = x :=
    (SkewMonoidAlgebra.sum_def' x SkewMonoidAlgebra.single).symm.trans
      (SkewMonoidAlgebra.sum_single x)
  refine hx.symm.trans (Finset.sum_congr rfl fun g _ => ?_)
  simp only [coeff_mul_unit_zpow_toAdd]
  have hcoeff : SkewMonoidAlgebra.coeff x g = ∑ c ∈ graphValues T k x g,
      ClopenCoeff.of T k (c • LocallyConstant.charFn k (isClopen_graphDomain T k x g c)) := by
    apply (ClopenCoeff.of T k).symm.injective
    rw [map_sum]
    simp only [RingEquiv.symm_apply_apply]
    exact (sum_smul_charFn_graphDomain T k x g).symm
  rw [hcoeff]
  exact map_sum (AddMonoidHom.mk' (SkewMonoidAlgebra.single g) (SkewMonoidAlgebra.single_add g))
    _ _

end Graphs

/-! ## Sources and ranges -/

section SourceRange

variable {X : Type} [MetricSpace X] [CompactSpace X] (T : X ≃ₜ X) (k : Type) [Ring k]

theorem disjoint_zpow_image_chainRecurrentSet (a : ℤ) {W : Set X}
    (hW : Disjoint W (Dynamics.chainRecurrentSet ⇑T)) :
    Disjoint (⇑(T ^ a) '' W) (Dynamics.chainRecurrentSet ⇑T) := by
  rw [Set.disjoint_left]
  rintro _ ⟨w, hw, rfl⟩ hz
  have h := zpow_mem_chainRecurrentSet T (-a) _ hz
  rw [Dynamics.zpow_apply_zpow_apply, neg_add_cancel, zpow_zero, Homeomorph.one_apply] at h
  exact Set.disjoint_left.1 hW hw h

/-- The graph domains of an element of `I` miss `Y = CR(T)`. -/
theorem graphDomain_disjoint {x : ClopenCrossedProduct T k}
    (hx : x ∈ transientIdeal T k (Dynamics.image_chainRecurrentSet T)) {g : Multiplicative ℤ}
    {c : k} (hc : c ≠ 0) : Disjoint (graphDomain T k x g c) (Dynamics.chainRecurrentSet ⇑T) := by
  rw [Set.disjoint_left]
  intro z hz hzY
  exact hc (hz.symm.trans
    ((mem_transientIdeal_iff_forall_coeff T k (Dynamics.image_chainRecurrentSet T)).1 hx g z hzY))

/-- **The union of the sources and ranges** (tex 1489–1490): for each graph `(D, g)` of each
element of `F`, its source `D`, its range `T^{-g}(D)`, and the source and range of the inverse
graph `(T^{-g}(D), g⁻¹)`. -/
noncomputable def sourceRangeUnion (F : Finset (ClopenCrossedProduct T k)) : Set X :=
  ⋃ x ∈ F, ⋃ g ∈ SkewMonoidAlgebra.support x, ⋃ c ∈ graphValues T k x g,
    ((graphDomain T k x g c ∪ ⇑(T ^ (-toAdd g)) '' graphDomain T k x g c) ∪
      (⇑(T ^ (-toAdd g)) '' graphDomain T k x g c ∪
        ⇑(T ^ (-toAdd g⁻¹)) '' (⇑(T ^ (-toAdd g)) '' graphDomain T k x g c)))

theorem isClopen_sourceRangeUnion (F : Finset (ClopenCrossedProduct T k)) :
    IsClopen (sourceRangeUnion T k F) :=
  isClopen_biUnion_finset fun x _ => isClopen_biUnion_finset fun g _ =>
    isClopen_biUnion_finset fun c _ =>
      ((isClopen_graphDomain T k x g c).union
          (Dynamics.isClopen_zpow_image T _ (isClopen_graphDomain T k x g c))).union
        ((Dynamics.isClopen_zpow_image T _ (isClopen_graphDomain T k x g c)).union
          (Dynamics.isClopen_zpow_image T _
            (Dynamics.isClopen_zpow_image T _ (isClopen_graphDomain T k x g c))))

theorem disjoint_sourceRangeUnion (F : Finset (ClopenCrossedProduct T k))
    (hF : ∀ x ∈ F, x ∈ transientIdeal T k (Dynamics.image_chainRecurrentSet T)) :
    Disjoint (sourceRangeUnion T k F) (Dynamics.chainRecurrentSet ⇑T) := by
  rw [Set.disjoint_left]
  intro z hz hzY
  simp only [sourceRangeUnion, Set.mem_iUnion, Set.mem_union] at hz
  obtain ⟨x, hx, g, -, c, hc, hz⟩ := hz
  have hD := graphDomain_disjoint T k (hF x hx) (g := g) ((mem_graphValues T k).1 hc).1
  have hI := disjoint_zpow_image_chainRecurrentSet T (-toAdd g) hD
  have hII := disjoint_zpow_image_chainRecurrentSet T (-toAdd g⁻¹) hI
  rcases hz with (hz | hz) | (hz | hz)
  · exact Set.disjoint_left.1 hD hz hzY
  · exact Set.disjoint_left.1 hI hz hzY
  · exact Set.disjoint_left.1 hI hz hzY
  · exact Set.disjoint_left.1 hII hz hzY

/-- Every nonzero coefficient of an element of `F` has its source and its range in the union. -/
theorem mem_sourceRangeUnion {F : Finset (ClopenCrossedProduct T k)} {x : ClopenCrossedProduct T k}
    (hx : x ∈ F) (g : Multiplicative ℤ) (z : X)
    (hz : (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g) z ≠ 0) :
    z ∈ sourceRangeUnion T k F ∧ (T ^ (-toAdd g)) z ∈ sourceRangeUnion T k F := by
  have hg : g ∈ SkewMonoidAlgebra.support x := SkewMonoidAlgebra.mem_support_iff.2 fun h0 =>
    hz (by rw [h0, map_zero, LocallyConstant.zero_apply])
  have hc : coeffFn T k x g z ∈ graphValues T k x g := (mem_graphValues T k).2 ⟨hz, z, rfl⟩
  have hzD : z ∈ graphDomain T k x g (coeffFn T k x g z) := rfl
  refine ⟨?_, ?_⟩ <;> simp only [sourceRangeUnion, Set.mem_iUnion, Set.mem_union]
  · exact ⟨x, hx, g, hg, _, hc, Or.inl (Or.inl hzD)⟩
  · exact ⟨x, hx, g, hg, _, hc, Or.inl (Or.inr ⟨z, hzD, rfl⟩)⟩

/-- **The cells of `lem:transient-matrices` over the union of sources and ranges** (tex 1489–1511):
as `exists_transientCells`, with `C = sourceRangeUnion T k F`. -/
theorem exists_transientCells_sourceRangeUnion [TotallyDisconnectedSpace X]
    (F : Finset (ClopenCrossedProduct T k))
    (hF : ∀ x ∈ F, x ∈ transientIdeal T k (Dynamics.image_chainRecurrentSet T)) :
    ∃ (E : Finset ℤ) (m M : ℕ) (cell : Fin M → Set X) (S : Fin M → Finset ℤ)
      (_ : ∀ a, IsClopen (cell a)) (rep : Fin M → X),
      IsClopen (sourceRangeUnion T k F) ∧
      Disjoint (sourceRangeUnion T k F) (Dynamics.chainRecurrentSet ⇑T) ∧
      ExponentBound T (sourceRangeUnion T k F) m ∧
      (∀ a, cell a ⊆ baseCell T (sourceRangeUnion T k F) E m (S a)) ∧
      (∀ a b, a ≠ b → Disjoint (cell a) (cell b)) ∧
      (∀ y ∈ baseSet T (sourceRangeUnion T k F) E m, ∃ a, y ∈ cell a) ∧
      (∀ a, rep a ∈ cell a) ∧
      (∀ x ∈ F, ∀ g ∈ SkewMonoidAlgebra.support x, toAdd g ∈ E ∧
        ∀ z, (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g) z ≠ 0 →
          z ∈ sourceRangeUnion T k F ∧ (T ^ (-toAdd g)) z ∈ sourceRangeUnion T k F) ∧
      ∀ x ∈ F, ∀ g ∈ SkewMonoidAlgebra.support x, ∀ a, ∀ d ∈ S a, ∀ y ∈ cell a, ∀ y' ∈ cell a,
        (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g) ((T ^ d) y) =
          (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g) ((T ^ d) y') := by
  classical
  have hK : IsClopen (sourceRangeUnion T k F) := isClopen_sourceRangeUnion T k F
  have hKY := disjoint_sourceRangeUnion T k F hF
  obtain ⟨m, W, -, hWw, hKW⟩ := exists_wandering_clopen_cover T
    (fun x hx => haveI : Nonempty X := ⟨x⟩; chainCoreDefectCoverStatement_holds X T x hx) hK hKY
  have hm : ExponentBound T (sourceRangeUnion T k F) m := exponentBound_of_wanderingCover hWw hKW
  obtain ⟨E, hEdef⟩ : ∃ E : Finset ℤ,
      E = F.biUnion fun x => (SkewMonoidAlgebra.support x).image toAdd := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : Finset (Multiplicative ℤ),
      G = F.biUnion fun x => SkewMonoidAlgebra.support x := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ := exists_finset_classExponents (T := T) (E := E) (m := m) hK
  obtain ⟨M, cell, S, hcell, hsub, hdisj, hne, hcov, hconst⟩ :=
    exists_cells (T := T) (E := E) (m := m) hK
      (ι := {x // x ∈ F} × {g // g ∈ G} × {d // d ∈ D})
      (fun p y => (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff p.1.1 p.2.1.1)
        ((T ^ p.2.2.1) y))
      fun p => ((ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff p.1.1 p.2.1.1)).isLocallyConstant
        |>.comp_continuous (T ^ p.2.2.1).continuous
  refine ⟨E, m, M, cell, S, hcell, fun a => (hne a).some, hK, hKY, hm, hsub, hdisj, hcov,
    fun a => (hne a).some_mem, fun x hx g hg => ⟨?_, fun z hz => mem_sourceRangeUnion T k hx g z hz⟩,
    fun x hx g hg a d hd y hy y' hy' => ?_⟩
  · rw [hEdef]
    exact Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image_of_mem _ hg⟩
  · have hyS : reachableExponents T (sourceRangeUnion T k F) E (m - 1) y = S a := (hsub a hy).2
    have hdD : d ∈ D := hD y (by rw [hyS]; exact hd)
    have hgG : g ∈ G := by
      rw [hGdef]
      exact Finset.mem_biUnion.2 ⟨x, hx, hg⟩
    exact hconst a y hy y' hy' (⟨x, hx⟩, ⟨g, hgG⟩, ⟨d, hdD⟩)

end SourceRange

/-! ## The printed statements -/

/-- **Printed (tex 1487–1489).**  "Express a prescribed finite subset of $I$ as linear combinations
of characteristic functions of compact clopen partial shift graphs": every `x ∈ I` is
`∑_{g ∈ G} ∑_{c ∈ V_g} c · 1_{D_{g,c}} u^g` with compact clopen domains missing `CR(T)`. -/
def PrintedPartialShiftGraphExpansion : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (k : Type) [Ring k] (x : ClopenCrossedProduct T k),
    x ∈ transientIdeal T k (Dynamics.image_chainRecurrentSet T) →
    ∃ (G : Finset (Multiplicative ℤ)) (V : Multiplicative ℤ → Finset k)
      (D : Multiplicative ℤ → k → Set X) (hD : ∀ g c, IsClopen (D g c)),
      (∀ g ∈ G, ∀ c ∈ V g, IsCompact (D g c) ∧ Disjoint (D g c) (Dynamics.chainRecurrentSet ⇑T)) ∧
      x = ∑ g ∈ G, ∑ c ∈ V g,
        coeff T k (c • LocallyConstant.charFn k (hD g c)) * ↑(unit T k ^ toAdd g)

theorem printedPartialShiftGraphExpansion : PrintedPartialShiftGraphExpansion := by
  intro X _ _ _ T k _ x hx
  exact ⟨SkewMonoidAlgebra.support x, graphValues T k x, graphDomain T k x,
    isClopen_graphDomain T k x, fun g _ c hc => ⟨(isClopen_graphDomain T k x g c).isClosed.isCompact,
      graphDomain_disjoint T k hx ((mem_graphValues T k).1 hc).1⟩, eq_sum_partialShiftGraphs T k x⟩

/-- **Printed (tex 1489–1490).**  "Include inverse partial shifts, and let $C$ be the union of their
sources and ranges": for a finite `F ⊆ I` the union of the sources and ranges of the graphs of `F`
and of their inverses is compact clopen, misses `CR(T)`, and contains the source and range of every
nonzero coefficient; the cells of the lemma exist over it. -/
def PrintedSourceRangeUnion : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (k : Type) [Ring k] (F : Finset (ClopenCrossedProduct T k)),
    (∀ x ∈ F, x ∈ transientIdeal T k (Dynamics.image_chainRecurrentSet T)) →
    IsClopen (sourceRangeUnion T k F) ∧ IsCompact (sourceRangeUnion T k F) ∧
      Disjoint (sourceRangeUnion T k F) (Dynamics.chainRecurrentSet ⇑T) ∧
      ∀ x ∈ F, ∀ (g : Multiplicative ℤ) (z : X),
        (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g) z ≠ 0 →
          z ∈ sourceRangeUnion T k F ∧ (T ^ (-toAdd g)) z ∈ sourceRangeUnion T k F

theorem printedSourceRangeUnion : PrintedSourceRangeUnion := by
  intro X _ _ _ T k _ F hF
  exact ⟨isClopen_sourceRangeUnion T k F, (isClopen_sourceRangeUnion T k F).isClosed.isCompact,
    disjoint_sourceRangeUnion T k F hF, fun x hx g z hz => mem_sourceRangeUnion T k hx g z hz⟩

/-- **The cells of the lemma with `C` the union of sources and ranges**, closed. -/
theorem transientCellsStatement_sourceRangeUnion : TransientCellsStatement := by
  intro X _ _ _ T k _ F hF
  obtain ⟨E, m, M, cell, S, hcell, rep, h⟩ := exists_transientCells_sourceRangeUnion T k F hF
  exact ⟨sourceRangeUnion T k F, E, m, M, cell, S, hcell, rep, h⟩

/-- **`I` is locally matricial**, along the cells over the union of sources and ranges. -/
theorem transientIdealLocallyMatricialStatement_sourceRangeUnion :
    TransientIdealLocallyMatricialStatement :=
  transientIdealLocallyMatricial_of_cells transientCellsStatement_sourceRangeUnion

end ClopenCrossedProduct

end GroupApproximation

#audit_closed_axioms GroupApproximation.Dynamics.printedFreenessUniqueArrow
#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.printedPartialShiftGraphExpansion
#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.printedSourceRangeUnion
#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.transientCellsStatement_sourceRangeUnion
#audit_closed_axioms
  GroupApproximation.ClopenCrossedProduct.transientIdealLocallyMatricialStatement_sourceRangeUnion
#audit_axioms GroupApproximation.ClopenCrossedProduct.eq_sum_partialShiftGraphs
#audit_axioms GroupApproximation.Dynamics.eq_of_zpow_apply_eq_of_not_mem_chainRecurrentSet
