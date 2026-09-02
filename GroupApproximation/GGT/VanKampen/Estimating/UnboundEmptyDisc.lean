import GroupApproximation.GGT.VanKampen.CactusBoundary
import GroupApproximation.GGT.VanKampen.Estimating.UnboundConstruction

/-!
# A disc diagram over the empty relator family, and two refutations

Osin's Appendix Lemma 62 (arXiv `math/0411039`, Lemma 62) is stated for a
reduced diagram `Delta` "which has `n >= 1` R-cells", under the additional
hypothesis `(*)` on the estimating graph, and after choosing `rho` large
against `mu`: the closing computation of Lemma 63 reads `rho > mu^{-2}`.

`EstimatingUnboundConstructionStatement` drops the cell-count hypothesis and
the parameter choice, so it is false.  This file supplies the witness.  The
single unoriented edge gives a planar closed map with one face, two vertices
and one edge, so it is a disc diagram whose relator-cell list is empty and
whose exterior word spells the identity.  The empty relator family satisfies
Osin's `C`-condition at every parameter value, and the exterior word is a
`(0,0)`-quasi-geodesic, so the diagram meets every hypothesis the statement
imposes.

Two independent fields of `Lemma62Data` then fail on it.  The strict budget
`unbound_lt` reads `0 < 0` when the relator-cell count is zero, and the
numerical field `threshold` reads `1 <= 0` when `mu` is zero.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Estimating

universe u w v

/-! ## Words whose letters all name the identity -/

/-- A word all of whose letters name the identity spells the identity after
reverse-inversion. -/
theorem listVal_revInv_of_val_one {G : Type u} [Group G] {Lambda : Type w}
    (word : List (GGT.RelLetter G Lambda))
    (hword : ∀ a ∈ word, a.val = (1 : G)) :
    GGT.RelLetter.listVal (HullSC.RelWord.revInv word) = 1 := by
  show ((HullSC.RelWord.revInv word).map GGT.RelLetter.val).prod = (1 : G)
  apply List.prod_eq_one
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  rw [HullSC.RelWord.revInv, List.mem_reverse, List.mem_map] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  rw [HullSC.RelWord.val_inv, hword a ha, inv_one]

/-! ## The one-edge closed map -/

/-- Edge reversal on the two darts of a single unoriented edge. -/
def emptyDiscAlpha : Equiv.Perm Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro b; cases b <;> rfl

/-- The one-edge rotation system: both endpoints have singleton `sigma`
orbits, so edge reversal is the face rotation and there is one face. -/
def emptyDiscMap : CombMap.{0} where
  Dart := Bool
  dartFintype := inferInstance
  alpha := emptyDiscAlpha
  sigma := 1
  alpha_involutive := by intro b; cases b <;> rfl
  alpha_fixedPointFree := by intro b; cases b <;> decide

/-- The one-edge map is connected through its unique edge. -/
theorem emptyDiscMap_isConnected : emptyDiscMap.IsConnected := by
  intro d e
  cases d <;> cases e
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.rel _ _ (Or.inl rfl)
  · exact Relation.EqvGen.rel _ _ (Or.inl rfl)
  · exact Relation.EqvGen.refl _

/-- Vertex orbits of the one-edge map are its two darts, since `sigma` is the
identity. -/
noncomputable def emptyDiscVertexEquiv : emptyDiscMap.Vertex ≃ Bool :=
  OrbitClassifier.orbitEquiv emptyDiscMap.sigma id id
    (by intro d; rfl) (by intro d; rfl)
    (by intro d; exact Equiv.Perm.SameCycle.rfl)

/-- The edge quotient of the one-edge map is a singleton. -/
noncomputable def emptyDiscEdgeEquiv : emptyDiscMap.Edge ≃ PUnit.{1} where
  toFun := fun _ ↦ PUnit.unit
  invFun := fun _ ↦ Quotient.mk'' false
  left_inv q := by
    refine Quotient.inductionOn' q ?_
    intro d
    apply Quotient.sound
    cases d
    · exact Or.inl rfl
    · exact Or.inr rfl
  right_inv _ := rfl

/-- The face quotient of the one-edge map is a singleton. -/
noncomputable def emptyDiscFaceEquiv : emptyDiscMap.Face ≃ PUnit.{1} where
  toFun := fun _ ↦ PUnit.unit
  invFun := fun _ ↦ Quotient.mk'' false
  left_inv q := by
    refine Quotient.inductionOn' q ?_
    intro d
    apply Quotient.sound
    cases d
    · exact Equiv.Perm.SameCycle.rfl
    · refine ⟨1, ?_⟩
      rfl
  right_inv _ := rfl

theorem emptyDiscMap_vertexCount : emptyDiscMap.vertexCount = 2 := by
  rw [CombMap.vertexCount, Nat.card_congr emptyDiscVertexEquiv,
    Nat.card_eq_fintype_card]
  exact Fintype.card_bool

theorem emptyDiscMap_edgeCount : emptyDiscMap.edgeCount = 1 := by
  rw [CombMap.edgeCount, Nat.card_congr emptyDiscEdgeEquiv,
    Nat.card_eq_fintype_card]
  exact Fintype.card_punit

theorem emptyDiscMap_faceCount : emptyDiscMap.faceCount = 1 := by
  rw [CombMap.faceCount, Nat.card_congr emptyDiscFaceEquiv,
    Nat.card_eq_fintype_card]
  exact Fintype.card_punit

/-- Euler's formula `2 - 1 + 1 = 2` for the one-edge map. -/
theorem emptyDiscMap_planar : emptyDiscMap.IsPlanar := by
  refine ⟨emptyDiscMap_isConnected, ?_⟩
  rw [CombMap.eulerCharacteristic, emptyDiscMap_vertexCount,
    emptyDiscMap_edgeCount, emptyDiscMap_faceCount]
  norm_num

/-- Every face of the one-edge map is its unique face. -/
theorem emptyDiscMap_face_eq (f : emptyDiscMap.Face) :
    f = emptyDiscMap.faceOf false := by
  refine Quotient.inductionOn' f ?_
  intro d
  apply Quotient.sound
  cases d
  · exact Equiv.Perm.SameCycle.rfl
  · refine ⟨1, ?_⟩
    rfl

/-- The canonical two-dart traversal, transported to the unique face. -/
noncomputable def emptyDiscFaceBoundary (f : emptyDiscMap.Face) :
    FaceBoundary emptyDiscMap f := by
  have hface : emptyDiscMap.faceOf false = f := (emptyDiscMap_face_eq f).symm
  exact hface ▸ FaceBoundary.based emptyDiscMap false

/-! ## The disc diagram over the empty relator family -/

/-- A planar disc with one unoriented edge, one exterior face, and no relator
cells.  Every dart carries the trivial letter of the peripheral subgroup
indexed by `lam`, so the exterior word spells the identity and the empty
relator product matches it. -/
noncomputable def emptyFamilyDisc {G : Type} [Group G] {Lambda : Type}
    (lam : Lambda) :
    DiscDiagram.{0, 0, 0} (∅ : Set (List (GGT.RelLetter G Lambda))) where
  toCombMap := emptyDiscMap
  planar := emptyDiscMap_planar
  label := fun _ ↦ GGT.RelLetter.comp lam 1
  label_alpha := by
    intro _
    show GGT.RelLetter.comp lam (1 : G) = GGT.RelLetter.comp lam (1 : G)⁻¹
    rw [inv_one]
  outerFace := emptyDiscMap.faceOf false
  faceBoundary := emptyDiscFaceBoundary
  relatorCells := []
  relatorCell_faces_nodup := List.nodup_nil
  relatorCell_word := by
    intro _ hC
    exact absurd hC List.not_mem_nil
  inner_face := by
    intro f hf
    exact (hf (emptyDiscMap_face_eq f)).elim
  boundary_product := by
    rw [List.map_nil, List.prod_nil]
    symm
    apply listVal_revInv_of_val_one
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨d, _, rfl⟩ := ha
    rfl

/-- The empty relator family leaves the diagram with no relator cells. -/
theorem emptyFamilyDisc_rCellCount {G : Type} [Group G] {Lambda : Type}
    (lam : Lambda) :
    (emptyFamilyDisc (G := G) (Lambda := Lambda) lam).rCellCount = 0 := rfl

/-- Every letter of the exterior word is the formal inverse of the trivial
peripheral letter. -/
theorem emptyFamilyDisc_mem_boundaryWord {G : Type} [Group G] {Lambda : Type}
    (lam : Lambda) {a : GGT.RelLetter G Lambda}
    (ha : a ∈ (emptyFamilyDisc (G := G) (Lambda := Lambda) lam).boundaryWord) :
    a = GGT.RelLetter.comp lam ((1 : G)⁻¹) := by
  rw [DiscDiagram.boundaryWord, HullSC.RelWord.revInv, List.mem_reverse,
    List.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  rw [DiscDiagram.faceWord, List.mem_map] at hb
  obtain ⟨d, _, rfl⟩ := hb
  rfl

/-- The exterior word of the one-edge disc is admissible for every relative
generating set with the index `lam`. -/
theorem emptyFamilyDisc_boundary_admissible {G : Type} [Group G]
    {Lambda : Type} (D : GGT.RelGenSet G Lambda) (lam : Lambda) :
    HullSC.RelWord.IsAdmissible D
      (emptyFamilyDisc (G := G) (Lambda := Lambda) lam).boundaryWord := by
  intro a ha
  rw [emptyFamilyDisc_mem_boundaryWord lam ha]
  show ((1 : G)⁻¹) ∈ D.fam lam
  rw [inv_one]
  exact (D.fam lam).one_mem

/-- The exterior word of the one-edge disc is a `(0,0)`-quasi-geodesic: the
lower bound it has to beat is zero. -/
theorem emptyFamilyDisc_quasiGeodesic {G : Type} [Group G] {Lambda : Type}
    (D : GGT.RelGenSet G Lambda) (lam : Lambda) :
    IsLambdaCQuasiGeodesicWord D 0 0
      (emptyFamilyDisc (G := G) (Lambda := Lambda) lam).boundaryWord := by
  refine ⟨emptyFamilyDisc_boundary_admissible D lam, ?_⟩
  intro i j _ _
  have hzero : (0 : ℝ) * ((j - i : ℕ) : ℝ) - 0 ≤ 0 := by norm_num
  exact le_trans hzero (Nat.cast_nonneg _)

/-! ## The two failing fields of `Lemma62Data` -/

/-- With no relator cells the strict budget field asks for `0 < 0`.  This is
Osin's standing hypothesis `n >= 1` in Lemma 62. -/
theorem no_lemma62Data_of_rCellCount_eq_zero {G : Type u} [Group G]
    {Lambda : Type w} {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {eps rho : ℕ} {mu : ℝ}
    {Delta : DiscDiagram.{u, w, v} W}
    {scaffold : EstimatingScaffold D eps Delta}
    (hzero : Delta.rCellCount = 0) :
    ¬ Nonempty (Lemma62Data D eps mu rho Delta scaffold) := by
  rintro ⟨data⟩
  have hlt := data.unbound_lt
  rw [hzero, Nat.cast_zero, zero_mul] at hlt
  have hnonneg : (0 : ℝ) ≤ (scaffold.partition.unboundTotal : ℝ) :=
    Nat.cast_nonneg _
  exact absurd hlt (not_lt.mpr hnonneg)

/-- At `mu = 0` the numerical field asks for `1 <= 0`.  This is Osin's
parameter choice `rho > mu^{-2}`, which the statement does not carry. -/
theorem no_lemma62Data_at_mu_zero {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {scaffold : EstimatingScaffold D eps Delta} :
    ¬ Nonempty (Lemma62Data D eps 0 rho Delta scaffold) := by
  rintro ⟨data⟩
  have hthreshold := data.threshold
  rw [mul_zero, zero_mul] at hthreshold
  norm_num at hthreshold

/-! ## The refutations -/

/-- `EstimatingUnboundConstructionStatement` fails on the one-edge disc at
`mu = 1`, `rho = 1`, where the numerical threshold `1 <= 2` holds and the
strict budget is the only failing field.  This isolates the missing
hypothesis `0 < Delta.rCellCount`. -/
theorem not_estimatingUnboundConstructionStatement_cells {G : Type} [Group G]
    {Lambda : Type} (D : GGT.RelGenSet G Lambda) (lam : Lambda) :
    ¬ EstimatingUnboundConstructionStatement.{0, 0, 0} := by
  intro hstatement
  obtain ⟨scaffold⟩ :=
    exists_estimatingScaffold D 0 (emptyFamilyDisc (G := G) lam)
  have hdata := hstatement D 0 1 1 0 0 Nat.one_pos
    (osinCCondition_emptyFamilyModel D 0 1 1 0 0)
    (emptyFamilyDisc (G := G) lam) scaffold
    (emptyFamilyDisc_quasiGeodesic D lam)
  exact no_lemma62Data_of_rCellCount_eq_zero
    (emptyFamilyDisc_rCellCount (G := G) lam) hdata

/-- `EstimatingUnboundConstructionStatement` fails on the one-edge disc at
`mu = 0`, `rho = 1`, where the failing field is the numerical threshold.
This isolates the missing parameter choice relating `rho` to `mu`. -/
theorem not_estimatingUnboundConstructionStatement_threshold {G : Type}
    [Group G] {Lambda : Type} (D : GGT.RelGenSet G Lambda) (lam : Lambda) :
    ¬ EstimatingUnboundConstructionStatement.{0, 0, 0} := by
  intro hstatement
  obtain ⟨scaffold⟩ :=
    exists_estimatingScaffold D 0 (emptyFamilyDisc (G := G) lam)
  have hdata := hstatement D 0 1 0 0 0 Nat.one_pos
    (osinCCondition_emptyFamilyModel D 0 1 0 0 0)
    (emptyFamilyDisc (G := G) lam) scaffold
    (emptyFamilyDisc_quasiGeodesic D lam)
  exact no_lemma62Data_at_mu_zero hdata

/-! ## A relative generating set for the refutations -/

/-- The full peripheral family over a single index, used to instantiate the
refutations at a concrete relative generating set. -/
def fullPeripheral (G : Type) [Group G] : GGT.RelGenSet G PUnit.{1} where
  base := ∅
  fam := fun _ ↦ ⊤
  symmetricGenerating := by
    constructor
    · intro x hx
      rcases hx with hx | hx
      · exact absurd hx (Set.notMem_empty x)
      · obtain ⟨lam, hxlam⟩ := Set.mem_iUnion.mp hx
        exact Or.inr (Set.mem_iUnion.mpr ⟨lam, (⊤ : Subgroup G).inv_mem hxlam⟩)
    · refine eq_top_iff.mpr ?_
      intro x _
      apply Subgroup.subset_closure
      refine Or.inr (Set.mem_iUnion.mpr ⟨PUnit.unit, ?_⟩)
      exact Subgroup.mem_top x

/-- The refutation at a concrete relative generating set, so the two theorems
above are not vacuous. -/
theorem not_estimatingUnboundConstructionStatement :
    ¬ EstimatingUnboundConstructionStatement.{0, 0, 0} :=
  not_estimatingUnboundConstructionStatement_cells
    (fullPeripheral PUnit.{1}) PUnit.unit

end Estimating
end VanKampen
end GGT
end GroupApproximation
