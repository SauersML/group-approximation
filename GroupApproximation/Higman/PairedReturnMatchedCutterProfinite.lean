import GroupApproximation.Higman.PairedReturnLeftProductProfinite
import GroupApproximation.Higman.PairedReturnEdgeSeparable
import GroupApproximation.Higman.FreeLampFiniteBaseProfinite
import GroupApproximation.Higman.PairedReturnImageIntersectionRefinement
import GroupApproximation.Higman.MatchedSubgroupAmalgamWordReflection
import GroupApproximation.Higman.ProfiniteBenignProductSeparable

/-!
# Finite tests on the paired-return amalgam

The explicit finite readers separate every finite list of offending left
syllables at once.  Their combined finite quotient extends across the ambient
amalgam while retaining the free synchronization coordinate, and hence lands
in the finite-base two-stage HNN model used by the free-label action.
-/

namespace GroupApproximation
namespace Higman
namespace PairedReturnMatchedCutterProfinite

open Monoid
open scoped Pointwise
open PairedReturnCutter

/-- The left product set which controls every possible pinch in the matched
subamalgam normal form. -/
abbrev LeftProduct : Set PairedReturnGraphIntersection.P :=
  (Star.graphSub : Set PairedReturnGraphIntersection.P) *
    (PairedReturnGraphIntersection.M : Set PairedReturnGraphIntersection.P)

/-- The canonical left vertex subgroup of the paired-return ambient. -/
abbrev leftRange : Subgroup Ambient :=
  (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC).range

/-- The finite reader target attached to `q`. -/
abbrev ProductTestTarget (Q : Type) [Group Q] :=
  (Equiv.Perm (Q × Q) × Q) × Q

/-- Contrapositive, quotient-shaped form of the explicit reader theorem. -/
theorem exists_finite_hom_separating_leftProduct
    {z : PairedReturnGraphIntersection.P} (hz : z ∉ LeftProduct) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q)
        (q : PairedReturnGraphIntersection.P →* Q),
      ∀ g ∈ LeftProduct, q g ≠ q z := by
  by_contra hnone
  have hadherent : PairedReturnLeftProductProfinite.ProductAdherent z := by
    intro Q _ _ q
    by_contra htest
    apply hnone
    refine ⟨ProductTestTarget Q, inferInstance, inferInstance,
      PairedReturnLeftProductProfinite.productTest Q q, ?_⟩
    intro g hg
    exact fun heq ↦ htest ⟨g, hg, heq⟩
  exact hz
    (PairedReturnLeftProductProfinite.mem_graphSub_mul_edge_of_productAdherent
      hadherent)

/-- One finite quotient simultaneously separates every offending syllable in
a finite list from `graphSub * M`. -/
theorem exists_finite_hom_separating_leftProduct_list :
    ∀ l : List PairedReturnGraphIntersection.P,
      (∀ z ∈ l, z ∉ LeftProduct) →
      ∃ (Q : Type) (_ : Group Q) (_ : Finite Q)
          (q : PairedReturnGraphIntersection.P →* Q),
        ∀ z ∈ l, ∀ g ∈ LeftProduct, q g ≠ q z
  | [] => by
      intro _
      refine ⟨PUnit, inferInstance, inferInstance, 1, ?_⟩
      simp
  | z :: l => by
      intro hout
      obtain ⟨Q, hQgroup, hQfinite, q, hq⟩ :=
        exists_finite_hom_separating_leftProduct
          (hout z List.mem_cons_self)
      letI : Group Q := hQgroup
      letI : Finite Q := hQfinite
      obtain ⟨R, hRgroup, hRfinite, r, hr⟩ :=
        exists_finite_hom_separating_leftProduct_list l
          (fun y hy ↦ hout y (List.mem_cons_of_mem z hy))
      letI : Group R := hRgroup
      letI : Finite R := hRfinite
      refine ⟨Q × R, inferInstance, inferInstance, q.prod r, ?_⟩
      intro y hy g hg heq
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hq g hg (congrArg Prod.fst heq)
      · exact hr y hy g hg (congrArg Prod.snd heq)

/-- The simultaneous reader quotient preserves each offending syllable as an
actual nonmembership in the product of the two mapped left subgroups.  This is
the pointwise input used by the reduced-amalgam spelling: subsequent edge
adjustments cannot turn one of these syllables into a matched left syllable. -/
theorem exists_finite_hom_reflecting_leftProduct_list
    (l : List PairedReturnGraphIntersection.P)
    (hout : ∀ z ∈ l, z ∉ LeftProduct) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q)
        (q : PairedReturnGraphIntersection.P →* Q),
      ∀ z ∈ l,
        q z ∉
          (Star.graphSub.map q : Set Q) *
            (PairedReturnGraphIntersection.M.map q : Set Q) := by
  obtain ⟨Q, hQgroup, hQfinite, q, hq⟩ :=
    exists_finite_hom_separating_leftProduct_list l hout
  refine ⟨Q, hQgroup, hQfinite, q, ?_⟩
  intro z hz hmem
  obtain ⟨a, ha, m, hm, ham⟩ := hmem
  obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨m₀, hm₀, rfl⟩ := Subgroup.mem_map.mp hm
  apply hq z hz (a₀ * m₀)
  · exact ⟨a₀, ha₀, m₀, hm₀, rfl⟩
  · simpa only [map_mul] using ham

/-- A point outside the conjugator graph remains outside its image in one
finite quotient. -/
theorem exists_finite_hom_reflecting_graph
    {z : PairedReturnGraphIntersection.P} (hz : z ∉ Star.graphSub) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q)
        (q : PairedReturnGraphIntersection.P →* Q),
      q z ∉ Star.graphSub.map q := by
  by_contra hnone
  have hzClosure : z ∈ profiniteClosure Star.graphSub := by
    intro Q _ _ q
    by_contra hout
    apply hnone
    exact ⟨Q, inferInstance, inferInstance, q, hout⟩
  rw [ConjugatorGraphProfinite.profiniteClosure_graphSub] at hzClosure
  exact hz hzClosure

/-- A point outside the paired edge remains outside its image in one finite
quotient. -/
theorem exists_finite_hom_reflecting_edge
    {z : PairedReturnGraphIntersection.P}
    (hz : z ∉ PairedReturnGraphIntersection.M) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q)
        (q : PairedReturnGraphIntersection.P →* Q),
      q z ∉ PairedReturnGraphIntersection.M.map q := by
  by_contra hnone
  have hzClosure : z ∈ profiniteClosure PairedReturnGraphIntersection.M := by
    intro Q _ _ q
    by_contra hout
    apply hnone
    exact ⟨Q, inferInstance, inferInstance, q, hout⟩
  rw [PairedReturnEdgeSeparable.profiniteClosure_edge] at hzClosure
  exact hz hzClosure

/-- One product quotient simultaneously preserves all offending left
syllables and a terminal failure to lie in the conjugator graph. -/
theorem exists_finite_hom_reflecting_leftProduct_list_and_graph
    (l : List PairedReturnGraphIntersection.P)
    (hout : ∀ z ∈ l, z ∉ LeftProduct)
    {e : PairedReturnGraphIntersection.P} (he : e ∉ Star.graphSub) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q)
        (q : PairedReturnGraphIntersection.P →* Q),
      (∀ z ∈ l,
        q z ∉ (Star.graphSub.map q : Set Q) *
          (PairedReturnGraphIntersection.M.map q : Set Q)) ∧
      q e ∉ Star.graphSub.map q := by
  obtain ⟨Q, hQgroup, hQfinite, q, hq⟩ :=
    exists_finite_hom_reflecting_leftProduct_list l hout
  letI : Group Q := hQgroup
  letI : Finite Q := hQfinite
  obtain ⟨R, hRgroup, hRfinite, r, hr⟩ :=
    exists_finite_hom_reflecting_graph he
  letI : Group R := hRgroup
  letI : Finite R := hRfinite
  refine ⟨Q × R, inferInstance, inferInstance, q.prod r, ?_, ?_⟩
  · intro z hz hmem
    obtain ⟨a, ha, m, hm, ham⟩ := hmem
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨m₀, hm₀, rfl⟩ := Subgroup.mem_map.mp hm
    apply hq z hz
    refine ⟨q a₀, ⟨a₀, ha₀, rfl⟩,
      q m₀, ⟨m₀, hm₀, rfl⟩, ?_⟩
    exact congrArg Prod.fst ham
  · intro hmem
    obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.mp hmem
    apply hr
    exact ⟨g, hg, congrArg Prod.snd hge⟩

/-- One finite quotient simultaneously preserves a finite list of failures
to lie in the conjugator graph. -/
theorem exists_finite_hom_reflecting_graph_list :
    ∀ l : List PairedReturnGraphIntersection.P,
      (∀ z ∈ l, z ∉ Star.graphSub) →
      ∃ (Q : Type) (_ : Group Q) (_ : Finite Q)
          (q : PairedReturnGraphIntersection.P →* Q),
        ∀ z ∈ l, q z ∉ Star.graphSub.map q
  | [] => by
      intro _
      refine ⟨PUnit, inferInstance, inferInstance, 1, ?_⟩
      simp
  | z :: l => by
      intro hout
      obtain ⟨Q, hQgroup, hQfinite, q, hq⟩ :=
        exists_finite_hom_reflecting_graph
          (hout z List.mem_cons_self)
      letI : Group Q := hQgroup
      letI : Finite Q := hQfinite
      obtain ⟨R, hRgroup, hRfinite, r, hr⟩ :=
        exists_finite_hom_reflecting_graph_list l
          (fun y hy ↦ hout y (List.mem_cons_of_mem z hy))
      letI : Group R := hRgroup
      letI : Finite R := hRfinite
      refine ⟨Q × R, inferInstance, inferInstance, q.prod r, ?_⟩
      intro y hy hmem
      obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.mp hmem
      rcases List.mem_cons.mp hy with rfl | hy
      · apply hq
        exact ⟨g, hg, congrArg Prod.fst hge⟩
      · apply hr y hy
        exact ⟨g, hg, congrArg Prod.snd hge⟩

/-- One finite quotient simultaneously preserves a finite list of failures
to lie in the paired edge. -/
theorem exists_finite_hom_reflecting_edge_list :
    ∀ l : List PairedReturnGraphIntersection.P,
      (∀ z ∈ l, z ∉ PairedReturnGraphIntersection.M) →
      ∃ (Q : Type) (_ : Group Q) (_ : Finite Q)
          (q : PairedReturnGraphIntersection.P →* Q),
        ∀ z ∈ l, q z ∉ PairedReturnGraphIntersection.M.map q
  | [] => by
      intro _
      refine ⟨PUnit, inferInstance, inferInstance, 1, ?_⟩
      simp
  | z :: l => by
      intro hout
      obtain ⟨Q, hQgroup, hQfinite, q, hq⟩ :=
        exists_finite_hom_reflecting_edge
          (hout z List.mem_cons_self)
      letI : Group Q := hQgroup
      letI : Finite Q := hQfinite
      obtain ⟨R, hRgroup, hRfinite, r, hr⟩ :=
        exists_finite_hom_reflecting_edge_list l
          (fun y hy ↦ hout y (List.mem_cons_of_mem z hy))
      letI : Group R := hRgroup
      letI : Finite R := hRfinite
      refine ⟨Q × R, inferInstance, inferInstance, q.prod r, ?_⟩
      intro y hy hmem
      obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.mp hmem
      rcases List.mem_cons.mp hy with rfl | hy
      · apply hq
        exact ⟨g, hg, congrArg Prod.fst hge⟩
      · apply hr y hy
        exact ⟨g, hg, congrArg Prod.snd hge⟩

/-- One product quotient simultaneously reflects two finite families: left
product failures and graph failures. -/
theorem exists_finite_hom_reflecting_leftProduct_list_and_graph_list
    (leftBad graphBad : List PairedReturnGraphIntersection.P)
    (hleft : ∀ z ∈ leftBad, z ∉ LeftProduct)
    (hgraph : ∀ z ∈ graphBad, z ∉ Star.graphSub) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q)
        (q : PairedReturnGraphIntersection.P →* Q),
      (∀ z ∈ leftBad,
        q z ∉ (Star.graphSub.map q : Set Q) *
          (PairedReturnGraphIntersection.M.map q : Set Q)) ∧
      (∀ z ∈ graphBad, q z ∉ Star.graphSub.map q) := by
  obtain ⟨Q, hQgroup, hQfinite, q, hq⟩ :=
    exists_finite_hom_reflecting_leftProduct_list leftBad hleft
  letI : Group Q := hQgroup
  letI : Finite Q := hQfinite
  obtain ⟨R, hRgroup, hRfinite, r, hr⟩ :=
    exists_finite_hom_reflecting_graph_list graphBad hgraph
  letI : Group R := hRgroup
  letI : Finite R := hRfinite
  refine ⟨Q × R, inferInstance, inferInstance, q.prod r, ?_, ?_⟩
  · intro z hz hmem
    obtain ⟨a, ha, m, hm, ham⟩ := hmem
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨m₀, hm₀, rfl⟩ := Subgroup.mem_map.mp hm
    apply hq z hz
    refine ⟨q a₀, ⟨a₀, ha₀, rfl⟩,
      q m₀, ⟨m₀, hm₀, rfl⟩, ?_⟩
    exact congrArg Prod.fst ham
  · intro z hz hmem
    obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.mp hmem
    apply hr z hz
    exact ⟨g, hg, congrArg Prod.snd hge⟩

/-- One product quotient preserves the left-product and terminal-graph
obstructions and also prevents every displayed left syllable from becoming
a new edge syllable. -/
theorem exists_finite_hom_reflecting_obstruction_lists
    (leftBad graphBad edgeBad : List PairedReturnGraphIntersection.P)
    (hleft : ∀ z ∈ leftBad, z ∉ LeftProduct)
    (hgraph : ∀ z ∈ graphBad, z ∉ Star.graphSub)
    (hedge : ∀ z ∈ edgeBad, z ∉ PairedReturnGraphIntersection.M) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q)
        (q : PairedReturnGraphIntersection.P →* Q),
      (∀ z ∈ leftBad,
        q z ∉ (Star.graphSub.map q : Set Q) *
          (PairedReturnGraphIntersection.M.map q : Set Q)) ∧
      (∀ z ∈ graphBad, q z ∉ Star.graphSub.map q) ∧
      (∀ z ∈ edgeBad,
        q z ∉ PairedReturnGraphIntersection.M.map q) := by
  obtain ⟨Q, hQgroup, hQfinite, q, hleftq, hgraphq⟩ :=
    exists_finite_hom_reflecting_leftProduct_list_and_graph_list
      leftBad graphBad hleft hgraph
  letI : Group Q := hQgroup
  letI : Finite Q := hQfinite
  obtain ⟨R, hRgroup, hRfinite, r, hedger⟩ :=
    exists_finite_hom_reflecting_edge_list edgeBad hedge
  letI : Group R := hRgroup
  letI : Finite R := hRfinite
  refine ⟨Q × R, inferInstance, inferInstance, q.prod r, ?_, ?_, ?_⟩
  · intro z hz hmem
    obtain ⟨a, ha, m, hm, ham⟩ := hmem
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨m₀, hm₀, rfl⟩ := Subgroup.mem_map.mp hm
    apply hleftq z hz
    refine ⟨q a₀, ⟨a₀, ha₀, rfl⟩,
      q m₀, ⟨m₀, hm₀, rfl⟩, ?_⟩
    exact congrArg Prod.fst ham
  · intro z hz hmem
    obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.mp hmem
    apply hgraphq z hz
    exact ⟨g, hg, congrArg Prod.fst hge⟩
  · intro z hz hmem
    obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.mp hmem
    apply hedger z hz
    exact ⟨g, hg, congrArg Prod.snd hge⟩

/-! ## The label-preserving finite-base quotient -/

/-- Restrict a quotient of `P` to the image of the paired edge. -/
def edgeToImage (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) :
    Edge →* PairedReturnGraphIntersection.M.map q :=
  (q.comp edgeToP).codRestrict _ fun e ↦ ⟨(e : _), e.property, rfl⟩

/-- Quotient the edge coordinate of the right vertex and retain its free
synchronization coordinate. -/
def rightToImageLamp (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) :
    C →* PairedReturnGraphIntersection.M.map q × Sync :=
  ((edgeToImage Q q).comp (MonoidHom.fst Edge Sync)).prod
    (MonoidHom.snd Edge Sync)

/-- The image of the synchronized right subgroup in the quotient lamp
factor. -/
def imageRightSub (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) :
    Subgroup (PairedReturnGraphIntersection.M.map q × Sync) :=
  PairedReturnCutter.Q.map (rightToImageLamp Q q)

/-- Retaining the synchronization coordinate prevents new right pinches:
if an image of the synchronized right subgroup lands in the target edge,
then its edge coordinate already lies in the mapped conjugator graph. -/
theorem imageRightSub_comap_edge_le_graph
    (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) :
    (imageRightSub Q q).comap
        (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync false) ≤
      (Star.graphSub.map q).comap
        (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync true) := by
  rintro d hd
  obtain ⟨c, hc, hcd⟩ := Subgroup.mem_map.mp hd
  obtain ⟨w, rfl⟩ := hc
  have hpair :
      (edgeToImage Q q (PairedReturnGraphIntersection.muToM w),
          PairedFoldKernel.fold Sync w) = (d, 1) := hcd
  have hfold : PairedFoldKernel.fold Sync w = 1 :=
    congrArg Prod.snd hpair
  have hdelta : PairedReturnGraphIntersection.mu w ∈
      PairedReturnGraphIntersection.deltaSub :=
    PairedReturnGraphIntersection.fold_ker_le_mu_comap_deltaSub
      (MonoidHom.mem_ker.mpr hfold)
  refine ⟨PairedReturnGraphIntersection.mu w,
    PairedReturnGraphIntersection.deltaSub_le_graphSub hdelta, ?_⟩
  have hfirst := congrArg Prod.fst hpair
  change q (PairedReturnGraphIntersection.mu w) = (d : Q)
  exact congrArg Subtype.val hfirst

/-- The returning subgroup, intrinsically inside the mapped edge. -/
def imageDelta (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) :
    Subgroup (PairedReturnGraphIntersection.M.map q) :=
  (PairedReturnGraphIntersection.deltaSub.map q).comap
    (PairedReturnGraphIntersection.M.map q).subtype

/-- Exact graph/edge intersection, expressed as the left edge-comap needed
by the matched-subamalgam theorem. -/
theorem imageGraph_comap_edge_eq_imageDelta
    (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    (hinter : Star.graphSub.map q ⊓
        PairedReturnGraphIntersection.M.map q =
      PairedReturnGraphIntersection.deltaSub.map q) :
    (Star.graphSub.map q).comap
        (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync true) =
      imageDelta Q q := by
  ext d
  constructor
  · intro hd
    change (d : Q) ∈ Star.graphSub.map q at hd
    change (d : Q) ∈ PairedReturnGraphIntersection.deltaSub.map q
    rw [← hinter]
    exact Subgroup.mem_inf.mpr ⟨hd, d.property⟩
  · intro hd
    change (d : Q) ∈ PairedReturnGraphIntersection.deltaSub.map q at hd
    change (d : Q) ∈ Star.graphSub.map q
    rw [← hinter] at hd
    exact (Subgroup.mem_inf.mp hd).1

/-- Exact graph/edge intersection also forces the synchronized right image
to have precisely the same edge-comap. -/
theorem imageRightSub_comap_edge_eq_imageDelta
    (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    (hinter : Star.graphSub.map q ⊓
        PairedReturnGraphIntersection.M.map q =
      PairedReturnGraphIntersection.deltaSub.map q) :
    (imageRightSub Q q).comap
        (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync false) =
      imageDelta Q q := by
  apply le_antisymm
  · rw [← imageGraph_comap_edge_eq_imageDelta Q q hinter]
    exact imageRightSub_comap_edge_le_graph Q q
  · intro d hd
    change (d : Q) ∈ PairedReturnGraphIntersection.deltaSub.map q at hd
    obtain ⟨p, hp, hpd⟩ := Subgroup.mem_map.mp hd
    have hpM : p ∈ PairedReturnGraphIntersection.M :=
      PairedReturnGraphIntersection.deltaSub_le_M hp
    let m : Edge := ⟨p, hpM⟩
    have hmDelta : m ∈ PairedReturnGraphIntersection.Delta := hp
    have hcQ : edgeToC m ∈ PairedReturnCutter.Q := by
      have hmComap : m ∈ PairedReturnCutter.Q.comap edgeToC := by
        rw [PairedReturnCutter.Q_comap_edgeToC_eq_Delta]
        exact hmDelta
      exact hmComap
    refine Subgroup.mem_map.mpr ⟨edgeToC m, hcQ, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      exact hpd
    · rfl

/-- Inclusion of the target lamp factor. -/
def imageRightInclusion (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) :
    PairedReturnGraphIntersection.M.map q × Sync →*
      FreeLamp Q (PairedReturnGraphIntersection.M.map q) Sync :=
  PushoutI.of
    (φ := lampMap Q (PairedReturnGraphIntersection.M.map q) Sync) false

/-- Generator set of the mapped matched cutter, now regarded intrinsically
inside the finite-base free lamp. -/
abbrev ImageMatchedGeneratorSet (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) :
    Set (FreeLamp Q (PairedReturnGraphIntersection.M.map q) Sync) :=
  (imageRightInclusion Q q '' (imageRightSub Q q : Set _)) ∪
    (inAmbient Q (PairedReturnGraphIntersection.M.map q) Sync ''
      (Star.graphSub.map q : Set Q))

/-- The two matched factor subgroups in the quotient free-lamp diagram. -/
def imageMatchedFactorSubgroup (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) : ∀ b,
    Subgroup (LampFactor Q (PairedReturnGraphIntersection.M.map q) Sync b)
  | false => imageRightSub Q q
  | true => Star.graphSub.map q

theorem imageMatchedFactorSubgroup_comap_edge
    (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    (hinter : Star.graphSub.map q ⊓
        PairedReturnGraphIntersection.M.map q =
      PairedReturnGraphIntersection.deltaSub.map q) :
    ∀ b, (imageMatchedFactorSubgroup Q q b).comap
        (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync b) =
      imageDelta Q q
  | false => imageRightSub_comap_edge_eq_imageDelta Q q hinter
  | true => imageGraph_comap_edge_eq_imageDelta Q q hinter

/-- The two source-factor maps into the quotient free lamp. -/
def imageLampFactors (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) : ∀ b,
    Amalgam.fam PairedReturnGraphIntersection.P C b →*
      FreeLamp Q (PairedReturnGraphIntersection.M.map q) Sync
  | false =>
      (inAmbient Q (PairedReturnGraphIntersection.M.map q) Sync).comp q
  | true =>
      (PushoutI.of
        (φ := lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
        false).comp (rightToImageLamp Q q)

theorem imageLampFactors_comp (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) : ∀ b,
    (imageLampFactors Q q b).comp (Amalgam.famHom edgeToP edgeToC b) =
      (inAmbient Q (PairedReturnGraphIntersection.M.map q) Sync).comp
        (q.comp edgeToP) := by
  intro b
  cases b with
  | false => rfl
  | true =>
      apply MonoidHom.ext
      intro e
      change PushoutI.of
          (φ := lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
          false (edgeToImage Q q e, 1) =
        inAmbient Q (PairedReturnGraphIntersection.M.map q) Sync
          (q (edgeToP e))
      calc
        PushoutI.of
            (φ := lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
            false (edgeToImage Q q e, 1) =
          PushoutI.base
            (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
            (edgeToImage Q q e) :=
              PushoutI.of_apply_eq_base _ false (edgeToImage Q q e)
        _ = inAmbient Q (PairedReturnGraphIntersection.M.map q) Sync
            (q (edgeToP e)) :=
          (PushoutI.of_apply_eq_base _ true (edgeToImage Q q e)).symm

/-- A quotient of `P` extends to a map of free-lamp amalgams while retaining
the honest rank-two lamp.  The target has finite base whenever `Q` is finite,
which is the input needed by the finite-label HNN action. -/
def ambientToImageLamp (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) :
    Ambient →* FreeLamp Q (PairedReturnGraphIntersection.M.map q) Sync :=
  PushoutI.lift
    (imageLampFactors Q q)
    ((inAmbient Q (PairedReturnGraphIntersection.M.map q) Sync).comp
      (q.comp edgeToP)) (imageLampFactors_comp Q q)

@[simp] theorem ambientToImageLamp_left (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    (g : PairedReturnGraphIntersection.P) :
    ambientToImageLamp Q q
        (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC g) =
      inAmbient Q (PairedReturnGraphIntersection.M.map q) Sync (q g) := by
  exact PushoutI.lift_of _ _ _ _

@[simp] theorem ambientToImageLamp_right (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) (g : C) :
    ambientToImageLamp Q q
        (MatchedSubgroupAmalgam.bigInB edgeToP edgeToC g) =
      PushoutI.of
        (φ := lampMap Q (PairedReturnGraphIntersection.M.map q) Sync) false
        (rightToImageLamp Q q g) := by
  exact PushoutI.lift_of _ _ _ _

@[simp] theorem ambientToImageLamp_rightLamp (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) (s : Sync) :
    ambientToImageLamp Q q
        (MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (1, s)) =
      inLamp Q (PairedReturnGraphIntersection.M.map q) Sync s := by
  rw [ambientToImageLamp_right]
  apply congrArg
    (PushoutI.of
      (φ := lampMap Q (PairedReturnGraphIntersection.M.map q) Sync) false)
  apply Prod.ext
  · exact Subtype.ext (map_one (q.comp edgeToP))
  · rfl

theorem ambientToImageLamp_right_eq (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) (m : Edge) (s : Sync) :
    ambientToImageLamp Q q
        (MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (m, s)) =
      inAmbient Q (PairedReturnGraphIntersection.M.map q) Sync
          (q (edgeToP m)) *
        inLamp Q (PairedReturnGraphIntersection.M.map q) Sync s := by
  have hedge :
      MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (m, 1) =
        MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (edgeToP m) := by
    change PushoutI.of (φ := Amalgam.famHom edgeToP edgeToC) true
        (Amalgam.famHom edgeToP edgeToC true m) =
      PushoutI.of (φ := Amalgam.famHom edgeToP edgeToC) false
        (Amalgam.famHom edgeToP edgeToC false m)
    exact (PushoutI.of_apply_eq_base
      (Amalgam.famHom edgeToP edgeToC) true m).trans
        (PushoutI.of_apply_eq_base
          (Amalgam.famHom edgeToP edgeToC) false m).symm
  have hsource :
      MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (m, s) =
        MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (edgeToP m) *
          MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (1, s) := by
    calc
      MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (m, s) =
          MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (m, 1) *
            MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (1, s) := by
              rw [← map_mul]
              simp
      _ = MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (edgeToP m) *
            MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (1, s) := by
          rw [hedge]
  rw [hsource, map_mul, ambientToImageLamp_left,
    ambientToImageLamp_rightLamp]

/-- The mapped cutter is generated by the mapped synchronized right subgroup
and mapped graph inside the quotient free lamp. -/
theorem map_matchedCutter_eq_imageGeneratorClosure
    (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) :
    matchedCutter.map (ambientToImageLamp Q q) =
      Subgroup.closure (ImageMatchedGeneratorSet Q q) := by
  rw [matchedCutter, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨g, hg, rfl⟩ | ⟨c, hc, rfl⟩
    · right
      refine ⟨q g, ⟨g, hg, rfl⟩, ?_⟩
      exact ambientToImageLamp_left Q q g
    · left
      refine ⟨rightToImageLamp Q q c, ⟨c, hc, rfl⟩, ?_⟩
      exact ambientToImageLamp_right Q q c
  · rintro (⟨c', hc', rfl⟩ | ⟨g', hg', rfl⟩)
    · obtain ⟨c, hc, rfl⟩ := hc'
      refine ⟨MatchedSubgroupAmalgam.bigInB edgeToP edgeToC c,
        Or.inr ⟨c, hc, rfl⟩, ?_⟩
      exact ambientToImageLamp_right Q q c
    · obtain ⟨g, hg, rfl⟩ := hg'
      refine ⟨MatchedSubgroupAmalgam.bigInA edgeToP edgeToC g,
        Or.inl ⟨g, hg, rfl⟩, ?_⟩
      exact ambientToImageLamp_left Q q g

/-- Under exact mapped edge intersection, the mapped cutter is literally the
range of the corresponding matched small-amalgam embedding. -/
theorem map_matchedCutter_eq_imageMatchedMap_range
    (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    (hinter : Star.graphSub.map q ⊓
        PairedReturnGraphIntersection.M.map q =
      PairedReturnGraphIntersection.deltaSub.map q) :
    matchedCutter.map (ambientToImageLamp Q q) =
      (MatchedSubgroupAmalgamWordReflection.IndexedMatched.matchedMap
        (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
        (imageMatchedFactorSubgroup Q q) (imageDelta Q q)
        (imageMatchedFactorSubgroup_comap_edge Q q hinter)).range := by
  rw [map_matchedCutter_eq_imageGeneratorClosure,
    MatchedSubgroupAmalgamWordReflection.IndexedMatched.matchedMap_range_eq_closure
        (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
        (imageMatchedFactorSubgroup Q q) (imageDelta Q q)
        (imageMatchedFactorSubgroup_comap_edge Q q hinter)]
  congr 1
  ext x
  constructor
  · rintro (hx | hx)
    · obtain ⟨s, hs, rfl⟩ := hx
      exact ⟨false, ⟨s, hs⟩, rfl⟩
    · obtain ⟨g, hg, rfl⟩ := hx
      exact ⟨true, ⟨g, hg⟩, rfl⟩
  · rintro ⟨b, s, rfl⟩
    cases b with
    | false =>
        change imageRightSub Q q at s
        exact Or.inl ⟨(s :
          PairedReturnGraphIntersection.M.map q × Sync), s.property, rfl⟩
    | true =>
        change Star.graphSub.map q at s
        exact Or.inr ⟨(s : Q), s.property, rfl⟩

/-! ## Edge-carry scanning -/

/-- A successful left-to-right scan carries one edge element between
successive factor syllables. -/
inductive EdgeScan : Edge →
    List (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b) →
    Edge → Prop
  | nil (e : Edge) : EdgeScan e [] e
  | left (e m tail : Edge) (g z : PairedReturnGraphIntersection.P)
      (l : List (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b))
      (hz : z ∈ Star.graphSub)
      (heq : (e : PairedReturnGraphIntersection.P) * g =
        z * (m : PairedReturnGraphIntersection.P))
      (hscan : EdgeScan m l tail) :
      EdgeScan e (⟨false, g⟩ :: l) tail
  | right (e m tail : Edge) (c t : C)
      (l : List (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b))
      (ht : t ∈ PairedReturnCutter.Q)
      (heq : edgeToC e * c = t * edgeToC m)
      (hscan : EdgeScan m l tail) :
      EdgeScan e (⟨true, c⟩ :: l) tail

/-- The scan invariant: a successfully scanned word is a cutter element
followed by the residual carried edge. -/
theorem factorization_of_edgeScan
    {e tail : Edge}
    {l : List (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b)}
    (hscan : EdgeScan e l tail) :
    ∃ h ∈ matchedCutter,
      MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (e : _) *
          MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC l =
        h * MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (tail : _) := by
  induction hscan with
  | nil e =>
      refine ⟨1, matchedCutter.one_mem, ?_⟩
      simp [MatchedSubgroupAmalgam.factorListProd]
  | left e m tail g z l hz heq hscan ih =>
      obtain ⟨h, hh, hfac⟩ := ih
      refine ⟨MatchedSubgroupAmalgam.bigInA edgeToP edgeToC z * h,
        matchedCutter.mul_mem
          (Subgroup.subset_closure (Or.inl ⟨z, hz, rfl⟩)) hh, ?_⟩
      change MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (e : _) *
          (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC g *
            MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC l) = _
      calc
        MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (e : _) *
              (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC g *
                MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC l) =
            MatchedSubgroupAmalgam.bigInA edgeToP edgeToC
              ((e : PairedReturnGraphIntersection.P) * g) *
                MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC l := by
                  rw [← mul_assoc, ← map_mul]
        _ = MatchedSubgroupAmalgam.bigInA edgeToP edgeToC
              (z * (m : PairedReturnGraphIntersection.P)) *
                MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC l := by rw [heq]
        _ = MatchedSubgroupAmalgam.bigInA edgeToP edgeToC z *
              (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (m : _) *
                MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC l) := by
                  rw [map_mul, mul_assoc]
        _ = MatchedSubgroupAmalgam.bigInA edgeToP edgeToC z *
              (h * MatchedSubgroupAmalgam.bigInA edgeToP edgeToC
                (tail : _)) := by rw [hfac]
        _ = (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC z * h) *
              MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (tail : _) := by
            exact (mul_assoc _ _ _).symm
  | right e m tail c t l ht heq hscan ih =>
      obtain ⟨h, hh, hfac⟩ := ih
      refine ⟨MatchedSubgroupAmalgam.bigInB edgeToP edgeToC t * h,
        matchedCutter.mul_mem
          (Subgroup.subset_closure (Or.inr ⟨t, ht, rfl⟩)) hh, ?_⟩
      change MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (e : _) *
          (MatchedSubgroupAmalgam.bigInB edgeToP edgeToC c *
            MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC l) = _
      have hedge :
          MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (e : _) =
            MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (edgeToC e) :=
        (PushoutI.of_apply_eq_base
          (Amalgam.famHom edgeToP edgeToC) false e).trans
          (PushoutI.of_apply_eq_base
            (Amalgam.famHom edgeToP edgeToC) true e).symm
      have htailEdge :
          MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (edgeToC m) =
            MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (m : _) :=
        (PushoutI.of_apply_eq_base
          (Amalgam.famHom edgeToP edgeToC) true m).trans
          (PushoutI.of_apply_eq_base
            (Amalgam.famHom edgeToP edgeToC) false m).symm
      rw [hedge]
      calc
        MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (edgeToC e) *
              (MatchedSubgroupAmalgam.bigInB edgeToP edgeToC c *
                MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC l) =
            MatchedSubgroupAmalgam.bigInB edgeToP edgeToC
              (edgeToC e * c) *
                MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC l := by
                rw [← mul_assoc, ← map_mul]
        _ = MatchedSubgroupAmalgam.bigInB edgeToP edgeToC
              (t * edgeToC m) *
                MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC l := by rw [heq]
        _ = MatchedSubgroupAmalgam.bigInB edgeToP edgeToC t *
              (MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (edgeToC m) *
                MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC l) := by
                  rw [map_mul, mul_assoc]
        _ = MatchedSubgroupAmalgam.bigInB edgeToP edgeToC t *
              (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (m : _) *
                MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC l) := by
                  rw [htailEdge]
        _ = MatchedSubgroupAmalgam.bigInB edgeToP edgeToC t *
              (h * MatchedSubgroupAmalgam.bigInA edgeToP edgeToC
                (tail : _)) := by rw [hfac]
        _ = (MatchedSubgroupAmalgam.bigInB edgeToP edgeToC t * h) *
              MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (tail : _) := by
            exact (mul_assoc _ _ _).symm

/-- Scanning a finite factor list either succeeds or stops at a carried left
syllable outside `graphSub * M`. -/
theorem exists_edgeScan_or_bad (e : Edge) :
    ∀ l : List (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b),
      (∃ tail, EdgeScan e l tail) ∨
      ∃ (pre : List
            (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b))
          (carry : Edge) (g : PairedReturnGraphIntersection.P)
          (rest : List
            (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b)),
        l = pre ++ ⟨false, g⟩ :: rest ∧
        EdgeScan e pre carry ∧
        (carry : PairedReturnGraphIntersection.P) * g ∉ LeftProduct
  | [] => Or.inl ⟨e, EdgeScan.nil e⟩
  | ⟨b, x⟩ :: l => by
      cases b with
      | false =>
          change PairedReturnGraphIntersection.P at x
          by_cases hx : (e : PairedReturnGraphIntersection.P) * x ∈ LeftProduct
          · obtain ⟨z, hz, m, hm, hzm⟩ := hx
            let ms : Edge := ⟨m, hm⟩
            rcases exists_edgeScan_or_bad ms l with hscan | hbad
            · obtain ⟨tail, htail⟩ := hscan
              exact Or.inl ⟨tail, EdgeScan.left e ms tail x z l hz
                hzm.symm htail⟩
            · obtain ⟨pre, carry, g, rest, hl, hpref, hfail⟩ := hbad
              refine Or.inr ⟨⟨false, x⟩ :: pre, carry, g, rest,
                ?_, ?_, hfail⟩
              · simp [hl]
              · exact EdgeScan.left e ms carry x z pre hz hzm.symm hpref
          · exact Or.inr ⟨[], e, x, l, rfl, EdgeScan.nil e, hx⟩
      | true =>
          change C at x
          obtain ⟨t, ht, m, hem⟩ :=
            PairedReturnQProfinite.exists_Q_mul_edge (edgeToC e * x)
          rcases exists_edgeScan_or_bad m l with hscan | hbad
          · obtain ⟨tail, htail⟩ := hscan
            exact Or.inl ⟨tail, EdgeScan.right e m tail x t l ht hem htail⟩
          · obtain ⟨pre, carry, g, rest, hl, hpref, hfail⟩ := hbad
            refine Or.inr ⟨⟨true, x⟩ :: pre, carry, g, rest,
              ?_, ?_, hfail⟩
            · simp [hl]
            · exact EdgeScan.right e m carry x t pre ht hem hpref

/-- A successful scan with graph-valued terminal edge reconstructs an
element of the matched cutter. -/
theorem normalWord_mem_matchedCutter_of_edgeScan
    {d : PushoutI.NormalWord.Transversal
      (Amalgam.famHom edgeToP edgeToC)}
    (w : PushoutI.NormalWord d) (tail : Edge)
    (hscan : EdgeScan w.head w.toWord.toList tail)
    (htail : (tail : PairedReturnGraphIntersection.P) ∈ Star.graphSub) :
    w.prod ∈ matchedCutter := by
  obtain ⟨h, hh, hfac⟩ := factorization_of_edgeScan hscan
  have hword :
      PushoutI.ofCoprodI w.toWord.prod =
        MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC
          w.toWord.toList :=
    MatchedSubgroupAmalgam.ofCoprodI_prod_eq_factorListProd
      edgeToP edgeToC w.toWord
  have hprod : w.prod =
      MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (w.head : _) *
        MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC
          w.toWord.toList := by
    rw [PushoutI.NormalWord.prod, hword]
    congr 1
    exact (PushoutI.of_apply_eq_base
      (Amalgam.famHom edgeToP edgeToC) false w.head).symm
  rw [hprod, hfac]
  exact matchedCutter.mul_mem hh
    (Subgroup.subset_closure (Or.inl
      ⟨(tail : PairedReturnGraphIntersection.P), htail, rfl⟩))

/-- An excluded normal word exposes either a bad carried left syllable or a
terminal edge outside the graph. -/
theorem exists_bad_or_terminal_of_normalWord_not_mem
    {d : PushoutI.NormalWord.Transversal
      (Amalgam.famHom edgeToP edgeToC)}
    (w : PushoutI.NormalWord d) (hw : w.prod ∉ matchedCutter) :
    (∃ (pre : List
          (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b))
        (carry : Edge) (g : PairedReturnGraphIntersection.P)
        (rest : List
          (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b)),
      w.toWord.toList = pre ++ ⟨false, g⟩ :: rest ∧
      EdgeScan w.head pre carry ∧
      (carry : PairedReturnGraphIntersection.P) * g ∉ LeftProduct) ∨
    ∃ tail, EdgeScan w.head w.toWord.toList tail ∧
      (tail : PairedReturnGraphIntersection.P) ∉ Star.graphSub := by
  rcases exists_edgeScan_or_bad w.head w.toWord.toList with hscan | hbad
  · obtain ⟨tail, htail⟩ := hscan
    right
    refine ⟨tail, htail, ?_⟩
    exact fun ht ↦ hw
      (normalWord_mem_matchedCutter_of_edgeScan w tail htail ht)
  · exact Or.inl hbad

/-! ## Right-to-left scans compatible with normal-form comparison -/

/-- A right-to-left scan writes each syllable as an edge element followed by
a matched-factor element.  Its terminal carry is fixed to `1`. -/
inductive RightEdgeScan :
    List (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b) →
    Edge → Prop
  | nil : RightEdgeScan [] 1
  | left (head tail : Edge) (g z : PairedReturnGraphIntersection.P)
      (l : List (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b))
      (hz : z ∈ Star.graphSub)
      (heq : g * (tail : PairedReturnGraphIntersection.P) =
        (head : PairedReturnGraphIntersection.P) * z)
      (hscan : RightEdgeScan l tail) :
      RightEdgeScan (⟨false, g⟩ :: l) head
  | right (head tail : Edge) (c t : C)
      (l : List (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b))
      (ht : t ∈ PairedReturnCutter.Q)
      (heq : c * edgeToC tail = edgeToC head * t)
      (hscan : RightEdgeScan l tail) :
      RightEdgeScan (⟨true, c⟩ :: l) head

/-- The right vertex also decomposes as an edge element followed by an
element of the synchronized subgroup. -/
theorem exists_edge_mul_Q (c : C) :
    ∃ e : Edge, ∃ t ∈ PairedReturnCutter.Q, c = edgeToC e * t := by
  obtain ⟨t, ht, e, heq⟩ :=
    PairedReturnQProfinite.exists_Q_mul_edge c⁻¹
  refine ⟨e⁻¹, t⁻¹, PairedReturnCutter.Q.inv_mem ht, ?_⟩
  calc
    c = (c⁻¹)⁻¹ := (inv_inv c).symm
    _ = (t * edgeToC e)⁻¹ := congrArg Inv.inv heq
    _ = edgeToC e⁻¹ * t⁻¹ := by simp

/-- A successful right scan factors the displayed word as its residual edge
followed by a matched-cutter element. -/
theorem factorization_of_rightEdgeScan
    {l : List (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b)}
    {head : Edge} (hscan : RightEdgeScan l head) :
    ∃ h ∈ matchedCutter,
      MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC l =
        MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (head : _) * h := by
  induction hscan with
  | nil =>
      refine ⟨1, matchedCutter.one_mem, ?_⟩
      simp [MatchedSubgroupAmalgam.factorListProd]
  | left head tail g z l hz heq hscan ih =>
      obtain ⟨h, hh, hfac⟩ := ih
      refine ⟨MatchedSubgroupAmalgam.bigInA edgeToP edgeToC z * h,
        matchedCutter.mul_mem
          (Subgroup.subset_closure (Or.inl ⟨z, hz, rfl⟩)) hh, ?_⟩
      change MatchedSubgroupAmalgam.bigInA edgeToP edgeToC g *
          MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC l = _
      rw [hfac, ← mul_assoc, ← map_mul, heq, map_mul, mul_assoc]
  | right head tail c t l ht heq hscan ih =>
      obtain ⟨h, hh, hfac⟩ := ih
      refine ⟨MatchedSubgroupAmalgam.bigInB edgeToP edgeToC t * h,
        matchedCutter.mul_mem
          (Subgroup.subset_closure (Or.inr ⟨t, ht, rfl⟩)) hh, ?_⟩
      change MatchedSubgroupAmalgam.bigInB edgeToP edgeToC c *
          MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC l = _
      rw [hfac]
      have htail :
          MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (tail : _) =
            MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (edgeToC tail) :=
        (PushoutI.of_apply_eq_base
          (Amalgam.famHom edgeToP edgeToC) false tail).trans
          (PushoutI.of_apply_eq_base
            (Amalgam.famHom edgeToP edgeToC) true tail).symm
      have hhead :
          MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (edgeToC head) =
            MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (head : _) :=
        (PushoutI.of_apply_eq_base
          (Amalgam.famHom edgeToP edgeToC) true head).trans
          (PushoutI.of_apply_eq_base
            (Amalgam.famHom edgeToP edgeToC) false head).symm
      rw [htail, ← mul_assoc, ← map_mul, heq, map_mul, hhead, mul_assoc]

/-- A successful right scan whose initial residual joins the normal-word head
inside the graph reconstructs a matched-cutter element. -/
theorem normalWord_mem_matchedCutter_of_rightEdgeScan
    {d : PushoutI.NormalWord.Transversal
      (Amalgam.famHom edgeToP edgeToC)}
    (w : PushoutI.NormalWord d) (head : Edge)
    (hscan : RightEdgeScan w.toWord.toList head)
    (hhead : (w.head : PairedReturnGraphIntersection.P) * (head : _) ∈
      Star.graphSub) :
    w.prod ∈ matchedCutter := by
  obtain ⟨h, hh, hfac⟩ := factorization_of_rightEdgeScan hscan
  have hword : PushoutI.ofCoprodI w.toWord.prod =
      MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC
        w.toWord.toList :=
    MatchedSubgroupAmalgam.ofCoprodI_prod_eq_factorListProd
      edgeToP edgeToC w.toWord
  have hbase : PushoutI.base (Amalgam.famHom edgeToP edgeToC) w.head =
      MatchedSubgroupAmalgam.bigInA edgeToP edgeToC
        (w.head : PairedReturnGraphIntersection.P) :=
    (PushoutI.of_apply_eq_base
      (Amalgam.famHom edgeToP edgeToC) false w.head).symm
  rw [PushoutI.NormalWord.prod, hword, hfac, ← mul_assoc,
    hbase, ← map_mul]
  exact matchedCutter.mul_mem
    (Subgroup.subset_closure (Or.inl ⟨_, hhead, rfl⟩)) hh

/-- Scanning from the right either succeeds or stops at a left syllable whose
product with the already-scanned edge carry lies outside `M * graphSub`. -/
theorem exists_rightEdgeScan_or_bad :
    ∀ l : List (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b),
      (∃ head, RightEdgeScan l head) ∨
      ∃ (pre : List
            (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b))
          (g : PairedReturnGraphIntersection.P) (rest : List
            (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b))
          (tail : Edge),
        l = pre ++ ⟨false, g⟩ :: rest ∧
        RightEdgeScan rest tail ∧
        g * (tail : PairedReturnGraphIntersection.P) ∉
          (PairedReturnGraphIntersection.M : Set _) *
            (Star.graphSub : Set PairedReturnGraphIntersection.P)
  | [] => Or.inl ⟨1, RightEdgeScan.nil⟩
  | ⟨b, x⟩ :: l => by
      rcases exists_rightEdgeScan_or_bad l with hscan | hbad
      · obtain ⟨tail, htail⟩ := hscan
        cases b with
        | false =>
            change PairedReturnGraphIntersection.P at x
            by_cases hx : x * (tail : PairedReturnGraphIntersection.P) ∈
                (PairedReturnGraphIntersection.M : Set _) *
                  (Star.graphSub : Set PairedReturnGraphIntersection.P)
            · obtain ⟨m, hm, z, hz, hmz⟩ := hx
              let head : Edge := ⟨m, hm⟩
              exact Or.inl ⟨head,
                RightEdgeScan.left head tail x z l hz hmz.symm htail⟩
            · exact Or.inr ⟨[], x, l, tail, rfl, htail, hx⟩
        | true =>
            change C at x
            obtain ⟨head, t, ht, heq⟩ :=
              exists_edge_mul_Q (x * edgeToC tail)
            exact Or.inl ⟨head,
              RightEdgeScan.right head tail x t l ht heq htail⟩
      · obtain ⟨pre, g, rest, tail, hl, hrest, hfail⟩ := hbad
        exact Or.inr ⟨⟨b, x⟩ :: pre, g, rest, tail,
          by simp [hl], hrest, hfail⟩

/-- Outside the product of the left vertex and the matched cutter, the
right-to-left scan must stop at a bad left syllable.  The terminal condition
disappears because an arbitrary residual edge is absorbed by the left
factor. -/
theorem exists_rightBad_of_normalWord_not_mem_leftRange_mul_matchedCutter
    {d : PushoutI.NormalWord.Transversal
      (Amalgam.famHom edgeToP edgeToC)}
    (w : PushoutI.NormalWord d)
    (hw : w.prod ∉ (leftRange : Set Ambient) * (matchedCutter : Set Ambient)) :
    ∃ (pre : List
          (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b))
        (g : PairedReturnGraphIntersection.P) (rest : List
          (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b))
        (tail : Edge),
      w.toWord.toList = pre ++ ⟨false, g⟩ :: rest ∧
      pre ≠ [] ∧
      RightEdgeScan rest tail ∧
      g * (tail : PairedReturnGraphIntersection.P) ∉
        (PairedReturnGraphIntersection.M : Set _) *
          (Star.graphSub : Set PairedReturnGraphIntersection.P) := by
  rcases exists_rightEdgeScan_or_bad w.toWord.toList with hscan | hbad
  · obtain ⟨head, hhead⟩ := hscan
    obtain ⟨h, hh, hfac⟩ := factorization_of_rightEdgeScan hhead
    exfalso
    apply hw
    refine ⟨
      MatchedSubgroupAmalgam.bigInA edgeToP edgeToC
        ((w.head : PairedReturnGraphIntersection.P) * (head : _)),
      ⟨_, rfl⟩, h, hh, ?_⟩
    have hword : PushoutI.ofCoprodI w.toWord.prod =
        MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC
          w.toWord.toList :=
      MatchedSubgroupAmalgam.ofCoprodI_prod_eq_factorListProd
        edgeToP edgeToC w.toWord
    have hbase : PushoutI.base (Amalgam.famHom edgeToP edgeToC) w.head =
        MatchedSubgroupAmalgam.bigInA edgeToP edgeToC
          (w.head : PairedReturnGraphIntersection.P) :=
      (PushoutI.of_apply_eq_base
        (Amalgam.famHom edgeToP edgeToC) false w.head).symm
    rw [PushoutI.NormalWord.prod, hword, hfac, hbase, ← mul_assoc,
      ← map_mul]
  · obtain ⟨pre, g, rest, tail, hlist, hscan, hfail⟩ := hbad
    refine ⟨pre, g, rest, tail, hlist, ?_, hscan, hfail⟩
    intro hpre
    subst pre
    obtain ⟨h, hh, hfac⟩ := factorization_of_rightEdgeScan hscan
    apply hw
    refine ⟨
      MatchedSubgroupAmalgam.bigInA edgeToP edgeToC
        ((w.head : PairedReturnGraphIntersection.P) * g * (tail : _)),
      ⟨_, rfl⟩, h, hh, ?_⟩
    have hword : PushoutI.ofCoprodI w.toWord.prod =
        MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC
          w.toWord.toList :=
      MatchedSubgroupAmalgam.ofCoprodI_prod_eq_factorListProd
        edgeToP edgeToC w.toWord
    have hbase : PushoutI.base (Amalgam.famHom edgeToP edgeToC) w.head =
        MatchedSubgroupAmalgam.bigInA edgeToP edgeToC
          (w.head : PairedReturnGraphIntersection.P) :=
      (PushoutI.of_apply_eq_base
        (Amalgam.famHom edgeToP edgeToC) false w.head).symm
    rw [PushoutI.NormalWord.prod, hword, hlist, List.nil_append,
      MatchedSubgroupAmalgam.factorListProd, hfac, hbase]
    have hg : PushoutI.of
          (φ := Amalgam.famHom edgeToP edgeToC) false g =
        MatchedSubgroupAmalgam.bigInA edgeToP edgeToC g := rfl
    rw [hg]
    simp only [map_mul, mul_assoc]

/-- An excluded normal word has either a right-scan bad syllable or a
terminal graph obstruction. -/
theorem exists_rightBad_or_terminal_of_normalWord_not_mem
    {d : PushoutI.NormalWord.Transversal
      (Amalgam.famHom edgeToP edgeToC)}
    (w : PushoutI.NormalWord d) (hw : w.prod ∉ matchedCutter) :
    (∃ (pre : List
          (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b))
        (g : PairedReturnGraphIntersection.P) (rest : List
          (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b))
        (tail : Edge),
      w.toWord.toList = pre ++ ⟨false, g⟩ :: rest ∧
      RightEdgeScan rest tail ∧
      g * (tail : PairedReturnGraphIntersection.P) ∉
        (PairedReturnGraphIntersection.M : Set _) *
          (Star.graphSub : Set PairedReturnGraphIntersection.P)) ∨
    ∃ head, RightEdgeScan w.toWord.toList head ∧
      (w.head : PairedReturnGraphIntersection.P) * (head : _) ∉
        Star.graphSub := by
  rcases exists_rightEdgeScan_or_bad w.toWord.toList with hscan | hbad
  · obtain ⟨head, hhead⟩ := hscan
    right
    refine ⟨head, hhead, ?_⟩
    exact fun hmem ↦ hw
      (normalWord_mem_matchedCutter_of_rightEdgeScan w head hhead hmem)
  · exact Or.inl hbad

/-- The left-factor syllables of a factor spelling. -/
def leftFactors :
    List (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b) →
      List PairedReturnGraphIntersection.P
  | [] => []
  | ⟨false, g⟩ :: l => g :: leftFactors l
  | ⟨true, _⟩ :: l => leftFactors l

theorem mem_leftFactors {g : PairedReturnGraphIntersection.P} :
    ∀ {l}, g ∈ leftFactors l → ⟨false, g⟩ ∈ l
  | [], h => by simp [leftFactors] at h
  | ⟨false, x⟩ :: l, h => by
      rw [leftFactors] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_leftFactors h)
  | ⟨true, x⟩ :: l, h => by
      rw [leftFactors] at h
      exact List.mem_cons_of_mem _ (mem_leftFactors h)

theorem left_mem_leftFactors {g : PairedReturnGraphIntersection.P} :
    ∀ {l}, ⟨false, g⟩ ∈ l → g ∈ leftFactors l
  | [], h => by simp at h
  | ⟨false, x⟩ :: l, h => by
      rw [leftFactors]
      rcases List.mem_cons.mp h with h | h
      · cases h
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (left_mem_leftFactors h)
  | ⟨true, x⟩ :: l, h => by
      rw [leftFactors]
      rcases List.mem_cons.mp h with h | h
      · simp at h
      · exact left_mem_leftFactors h

/-- Every displayed left syllable of a normal word is outside the paired
edge. -/
theorem leftFactors_not_mem_edge
    {d : PushoutI.NormalWord.Transversal
      (Amalgam.famHom edgeToP edgeToC)}
    (w : PushoutI.NormalWord d) :
    ∀ g ∈ leftFactors w.toWord.toList,
      g ∉ PairedReturnGraphIntersection.M := by
  intro g hg hgedge
  have hred := PushoutEmbedding.normalWord_reduced
    (Amalgam.famHom edgeToP edgeToC) d w
  apply hred ⟨false, g⟩ (mem_leftFactors hg)
  exact ⟨⟨g, hgedge⟩, rfl⟩

/-- Map a literal source syllable into the corresponding (oppositely indexed)
factor of the quotient free lamp. -/
def quotientLetter (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) :
    (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b) →
      (Σ b, LampFactor Q (PairedReturnGraphIntersection.M.map q) Sync b)
  | ⟨false, g⟩ => ⟨true, q g⟩
  | ⟨true, c⟩ => ⟨false, rightToImageLamp Q q c⟩

/-- If no displayed left syllable becomes an edge syllable, the literal
quotient spelling is still a coproduct word. -/
def quotientWord
    (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    (w : Monoid.CoprodI.Word
      (Amalgam.fam PairedReturnGraphIntersection.P C))
    (hred : PushoutI.Reduced
      (Amalgam.famHom edgeToP edgeToC) w)
    (hedge : ∀ g ∈ leftFactors w.toList,
      q g ∉ PairedReturnGraphIntersection.M.map q) :
    Monoid.CoprodI.Word
      (LampFactor Q (PairedReturnGraphIntersection.M.map q) Sync) where
  toList := w.toList.map (quotientLetter Q q)
  ne_one := by
    intro l hl
    obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hl
    rcases l₀ with ⟨b, x⟩
    cases b with
    | false =>
        change q x ≠ 1
        intro hx
        apply hedge x (left_mem_leftFactors hl₀)
        rw [hx]
        exact Subgroup.one_mem _
    | true =>
        change rightToImageLamp Q q x ≠ 1
        intro hx
        have hs := congrArg Prod.snd hx
        change x.2 = 1 at hs
        apply hred ⟨true, x⟩ hl₀
        refine ⟨x.1, ?_⟩
        exact Prod.ext rfl hs.symm
  chain_ne := by
    rw [List.isChain_map]
    refine w.chain_ne.imp ?_
    rintro ⟨b, x⟩ ⟨c, y⟩ h
    cases b <;> cases c <;> simp_all [quotientLetter]

/-- The quotient word is reduced in the target amalgam: left reducedness is
the finite edge test, while right reducedness is protected by the unchanged
synchronization coordinate. -/
theorem quotientWord_reduced
    (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    (w : Monoid.CoprodI.Word
      (Amalgam.fam PairedReturnGraphIntersection.P C))
    (hred : PushoutI.Reduced
      (Amalgam.famHom edgeToP edgeToC) w)
    (hedge : ∀ g ∈ leftFactors w.toList,
      q g ∉ PairedReturnGraphIntersection.M.map q) :
    PushoutI.Reduced
      (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
      (quotientWord Q q w hred hedge) := by
  intro l hl hrange
  obtain ⟨l₀, hl₀, heq⟩ := List.mem_map.mp hl
  cases heq
  rcases l₀ with ⟨b, x⟩
  cases b with
  | false =>
      obtain ⟨m, hm⟩ := hrange
      apply hedge x (left_mem_leftFactors hl₀)
      change (m : Q) = q x at hm
      rw [← hm]
      exact m.property
  | true =>
      obtain ⟨m, hm⟩ := hrange
      apply hred ⟨true, x⟩ hl₀
      refine ⟨x.1, ?_⟩
      change (m, (1 : Sync)) =
        (edgeToImage Q q x.1, x.2) at hm
      have hs : 1 = x.2 := congrArg Prod.snd hm
      apply Prod.ext
      · rfl
      · exact hs

/-- The quotient homomorphism evaluates a source factor list as the reversed-
index quotient factor list. -/
def imageFactorListProd (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) :
    List (Σ b, LampFactor Q
      (PairedReturnGraphIntersection.M.map q) Sync b) →
      FreeLamp Q (PairedReturnGraphIntersection.M.map q) Sync
  | [] => 1
  | ⟨b, x⟩ :: l =>
      PushoutI.of
        (φ := lampMap Q (PairedReturnGraphIntersection.M.map q) Sync) b x *
        imageFactorListProd Q q l

theorem ambientToImageLamp_factorListProd
    (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) :
    ∀ l : List (Σ b,
        Amalgam.fam PairedReturnGraphIntersection.P C b),
      ambientToImageLamp Q q
          (MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC l) =
        imageFactorListProd Q q (l.map (quotientLetter Q q))
  | [] => by simp [MatchedSubgroupAmalgam.factorListProd,
      imageFactorListProd]
  | ⟨b, x⟩ :: l => by
      cases b with
      | false =>
          change ambientToImageLamp Q q
              (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC x *
                MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC l) = _
          rw [map_mul, ambientToImageLamp_left,
            ambientToImageLamp_factorListProd Q q l]
          simp [imageFactorListProd, quotientLetter]
      | true =>
          change ambientToImageLamp Q q
              (MatchedSubgroupAmalgam.bigInB edgeToP edgeToC x *
                MatchedSubgroupAmalgam.factorListProd edgeToP edgeToC l) = _
          rw [map_mul, ambientToImageLamp_right,
            ambientToImageLamp_factorListProd Q q l]
          simp [imageFactorListProd, quotientLetter]

theorem imageFactorListProd_eq_ofCoprodI_prod
    (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    (w : Monoid.CoprodI.Word
      (LampFactor Q (PairedReturnGraphIntersection.M.map q) Sync)) :
    imageFactorListProd Q q w.toList = PushoutI.ofCoprodI w.prod := by
  induction w using Monoid.CoprodI.Word.consRecOn with
  | empty => simp [imageFactorListProd, Monoid.CoprodI.Word.prod]
  | @cons i g w hidx hg ih =>
      rw [Monoid.CoprodI.Word.prod_cons, map_mul,
        PushoutI.ofCoprodI_of]
      change PushoutI.of
          (φ := lampMap Q (PairedReturnGraphIntersection.M.map q) Sync) i g *
          imageFactorListProd Q q w.toList = _
      rw [ih]

/-- Evaluation of a source normal word agrees with the explicit reduced
quotient spelling and the mapped edge head. -/
theorem ambientToImageLamp_normalWord_prod
    (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    {d : PushoutI.NormalWord.Transversal
      (Amalgam.famHom edgeToP edgeToC)}
    (w : PushoutI.NormalWord d)
    (hred : PushoutI.Reduced
      (Amalgam.famHom edgeToP edgeToC) w.toWord)
    (hedge : ∀ g ∈ leftFactors w.toWord.toList,
      q g ∉ PairedReturnGraphIntersection.M.map q) :
    ambientToImageLamp Q q w.prod =
      PushoutI.base
          (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
          (edgeToImage Q q w.head) *
        PushoutI.ofCoprodI (quotientWord Q q w.toWord hred hedge).prod := by
  rw [PushoutI.NormalWord.prod, map_mul]
  have hhead : ambientToImageLamp Q q
        (PushoutI.base (Amalgam.famHom edgeToP edgeToC) w.head) =
      PushoutI.base
        (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
        (edgeToImage Q q w.head) := by
    rw [← PushoutI.of_apply_eq_base
      (Amalgam.famHom edgeToP edgeToC) false w.head,
      show PushoutI.of (φ := Amalgam.famHom edgeToP edgeToC) false
          (Amalgam.famHom edgeToP edgeToC false w.head) =
        MatchedSubgroupAmalgam.bigInA edgeToP edgeToC
          (edgeToP w.head) from rfl,
      ambientToImageLamp_left]
    exact PushoutI.of_apply_eq_base
      (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync) true
      (edgeToImage Q q w.head)
  rw [hhead,
    MatchedSubgroupAmalgam.ofCoprodI_prod_eq_factorListProd
      edgeToP edgeToC,
    ambientToImageLamp_factorListProd]
  change PushoutI.base
      (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
      (edgeToImage Q q w.head) *
      imageFactorListProd Q q
        (quotientWord Q q w.toWord hred hedge).toList = _
  rw [imageFactorListProd_eq_ofCoprodI_prod]

/-- A quotient preserves the source scan obstruction and prevents every
left normal syllable from collapsing into the target edge. -/
def PreservedObstruction
    (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    {d : PushoutI.NormalWord.Transversal
      (Amalgam.famHom edgeToP edgeToC)}
    (w : PushoutI.NormalWord d) : Prop :=
  ((∃ (pre : List
          (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b))
        (carry : Edge) (g : PairedReturnGraphIntersection.P)
        (rest : List
          (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b)),
      w.toWord.toList = pre ++ ⟨false, g⟩ :: rest ∧
      EdgeScan w.head pre carry ∧
      q ((carry : PairedReturnGraphIntersection.P) * g) ∉
        (Star.graphSub.map q : Set Q) *
          (PairedReturnGraphIntersection.M.map q : Set Q)) ∨
    ∃ tail, EdgeScan w.head w.toWord.toList tail ∧
      q (tail : PairedReturnGraphIntersection.P) ∉ Star.graphSub.map q) ∧
  ∀ g ∈ leftFactors w.toWord.toList,
    q g ∉ PairedReturnGraphIntersection.M.map q

/-- Every excluded element has a normal spelling and one finite quotient
preserving its scan obstruction while keeping the spelling reduced. -/
theorem exists_finite_hom_preserving_normalObstruction
    {z : Ambient} (hz : z ∉ matchedCutter) :
    ∃ (d : PushoutI.NormalWord.Transversal
          (Amalgam.famHom edgeToP edgeToC))
      (w : PushoutI.NormalWord d)
      (Q : Type) (_ : Group Q) (_ : Finite Q)
      (q : PairedReturnGraphIntersection.P →* Q),
      w.prod = z ∧ w.prod ∉ matchedCutter ∧
        PreservedObstruction Q q w := by
  classical
  letI : ∀ b : Bool,
      DecidableEq (Amalgam.fam PairedReturnGraphIntersection.P C b) :=
    fun _ ↦ Classical.decEq _
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty
    (Amalgam.famHom edgeToP edgeToC)
    (Amalgam.famHom_injective edgeToP edgeToC
      edgeToP_injective edgeToC_injective)
  let w : PushoutI.NormalWord d := PushoutI.NormalWord.equiv z
  have hwprod : w.prod = z :=
    (PushoutI.NormalWord.equiv (d := d)).symm_apply_apply z
  have hwout : w.prod ∉ matchedCutter := by rwa [hwprod]
  have hedge := leftFactors_not_mem_edge w
  rcases exists_bad_or_terminal_of_normalWord_not_mem w hwout with
      hbad | hterminal
  · obtain ⟨pre, carry, g, rest, hlist, hscan, hfail⟩ := hbad
    obtain ⟨Q, hQgroup, hQfinite, q, hleft, _, hedgeq⟩ :=
      exists_finite_hom_reflecting_obstruction_lists
        [(carry : PairedReturnGraphIntersection.P) * g] []
        (leftFactors w.toWord.toList) (by
          intro x hx
          rw [List.mem_singleton] at hx
          subst x
          exact hfail) (by simp) hedge
    refine ⟨d, w, Q, hQgroup, hQfinite, q, hwprod, hwout,
      Or.inl ⟨pre, carry, g, rest, hlist, hscan, ?_⟩, hedgeq⟩
    exact hleft ((carry : PairedReturnGraphIntersection.P) * g) (by simp)
  · obtain ⟨tail, hscan, htail⟩ := hterminal
    obtain ⟨Q, hQgroup, hQfinite, q, _, hgraph, hedgeq⟩ :=
      exists_finite_hom_reflecting_obstruction_lists []
        [(tail : PairedReturnGraphIntersection.P)]
        (leftFactors w.toWord.toList) (by simp) (by
          intro x hx
          rw [List.mem_singleton] at hx
          subst x
          exact htail) hedge
    refine ⟨d, w, Q, hQgroup, hQfinite, q, hwprod, hwout,
      Or.inr ⟨tail, hscan, ?_⟩, hedgeq⟩
    exact hgraph (tail : PairedReturnGraphIntersection.P) (by simp)

/-- A refined finite quotient preserves a right-scan obstruction, keeps the
displayed word reduced, and has exact graph/edge image intersection. -/
def RightPreservedObstruction
    (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    {d : PushoutI.NormalWord.Transversal
      (Amalgam.famHom edgeToP edgeToC)}
    (w : PushoutI.NormalWord d) : Prop :=
  ((∃ (pre : List
          (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b))
        (g : PairedReturnGraphIntersection.P) (rest : List
          (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b))
        (tail : Edge),
      w.toWord.toList = pre ++ ⟨false, g⟩ :: rest ∧
      RightEdgeScan rest tail ∧
      q ((g * (tail : PairedReturnGraphIntersection.P))⁻¹) ∉
        (Star.graphSub.map q : Set Q) *
          (PairedReturnGraphIntersection.M.map q : Set Q)) ∨
    ∃ head, RightEdgeScan w.toWord.toList head ∧
      q ((w.head : PairedReturnGraphIntersection.P) * (head : _)) ∉
        Star.graphSub.map q) ∧
  ∀ g ∈ leftFactors w.toWord.toList,
    q g ∉ PairedReturnGraphIntersection.M.map q

/-- A source right scan maps to a carry comparison whose comparison word lies
letterwise in the two target matched factor subgroups. -/
theorem exists_image_rightCarryComparison_of_rightEdgeScan
    (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) :
    ∀ {l : List
          (Σ b, Amalgam.fam PairedReturnGraphIntersection.P C b)}
      {head : Edge}, RightEdgeScan l head →
      ∃ small : List
          (Σ b, LampFactor Q
            (PairedReturnGraphIntersection.M.map q) Sync b),
        MatchedSubgroupAmalgamWordReflection.RightCarryComparison
          (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
          (l.map (quotientLetter Q q)) small (edgeToImage Q q head) ∧
        ∀ x ∈ small, x.2 ∈ imageMatchedFactorSubgroup Q q x.1 := by
  intro l head hscan
  induction hscan with
  | nil =>
      refine ⟨[], ?_, by simp⟩
      simpa using
        (MatchedSubgroupAmalgamWordReflection.RightCarryComparison.nil
          (φ := lampMap Q (PairedReturnGraphIntersection.M.map q) Sync))
  | left head tail g z l hz heq hscan ih =>
      obtain ⟨small, hcompare, hsmall⟩ := ih
      refine ⟨⟨true, q z⟩ :: small, ?_, ?_⟩
      · apply MatchedSubgroupAmalgamWordReflection.RightCarryComparison.cons
          true (q g) (q z) _ _ (edgeToImage Q q head)
            (edgeToImage Q q tail) _ hcompare
        change q g * q (tail : PairedReturnGraphIntersection.P) =
          q (head : PairedReturnGraphIntersection.P) * q z
        simpa only [map_mul] using congrArg q heq
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨z, hz, rfl⟩
        · exact hsmall x hx
  | right head tail c t l ht heq hscan ih =>
      obtain ⟨small, hcompare, hsmall⟩ := ih
      refine ⟨⟨false, rightToImageLamp Q q t⟩ :: small, ?_, ?_⟩
      · apply MatchedSubgroupAmalgamWordReflection.RightCarryComparison.cons
          false (rightToImageLamp Q q c) (rightToImageLamp Q q t)
            _ _ (edgeToImage Q q head) (edgeToImage Q q tail) _ hcompare
        change rightToImageLamp Q q c *
            rightToImageLamp Q q (edgeToC tail) =
          rightToImageLamp Q q (edgeToC head) * rightToImageLamp Q q t
        simpa only [map_mul] using congrArg (rightToImageLamp Q q) heq
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨t, ht, rfl⟩
        · exact hsmall x hx

/-- Membership in the mapped cutter produces a target carry comparison with
a word lying letterwise in the two mapped matched factor subgroups. -/
theorem exists_target_rightCarryComparison_of_map_mem
    (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    {d : PushoutI.NormalWord.Transversal
      (Amalgam.famHom edgeToP edgeToC)}
    (w : PushoutI.NormalWord d)
    (hred : PushoutI.Reduced
      (Amalgam.famHom edgeToP edgeToC) w.toWord)
    (hedge : ∀ g ∈ leftFactors w.toWord.toList,
      q g ∉ PairedReturnGraphIntersection.M.map q)
    (hinter : Star.graphSub.map q ⊓
        PairedReturnGraphIntersection.M.map q =
      PairedReturnGraphIntersection.deltaSub.map q)
    (hmem : ambientToImageLamp Q q w.prod ∈
      matchedCutter.map (ambientToImageLamp Q q)) :
    ∃ (small : List (Σ b,
          LampFactor Q (PairedReturnGraphIntersection.M.map q) Sync b))
      (smallHead : PairedReturnGraphIntersection.M.map q),
      MatchedSubgroupAmalgamWordReflection.RightCarryComparison
        (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
        (quotientWord Q q w.toWord hred hedge).toList small
        ((edgeToImage Q q w.head)⁻¹ * smallHead) ∧
      smallHead ∈ imageDelta Q q ∧
      ∀ x ∈ small, x.2 ∈ imageMatchedFactorSubgroup Q q x.1 := by
  have hrange : ambientToImageLamp Q q w.prod ∈
      (MatchedSubgroupAmalgamWordReflection.IndexedMatched.matchedMap
        (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
        (imageMatchedFactorSubgroup Q q) (imageDelta Q q)
        (imageMatchedFactorSubgroup_comap_edge Q q hinter)).range := by
    rw [← map_matchedCutter_eq_imageMatchedMap_range Q q hinter]
    exact hmem
  rw [ambientToImageLamp_normalWord_prod Q q w hred hedge] at hrange
  obtain ⟨dsmall, wsmall, hcompare⟩ :=
    MatchedSubgroupAmalgamWordReflection.IndexedMatched.exists_rightCarryComparison_of_mem_range
        (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
        (imageMatchedFactorSubgroup Q q) (imageDelta Q q)
        (lampMap_injective Q (PairedReturnGraphIntersection.M.map q) Sync)
        (imageMatchedFactorSubgroup_comap_edge Q q hinter)
        (quotientWord Q q w.toWord hred hedge)
        (quotientWord_reduced Q q w.toWord hred hedge)
        (edgeToImage Q q w.head) hrange
  let small := (PushoutEmbedding.wordMap
    (MatchedSubgroupAmalgamWordReflection.IndexedMatched.factorInclusion
      (imageMatchedFactorSubgroup Q q))
    (fun _ ↦ Subtype.val_injective)
    wsmall.toWord).toList
  let smallHead : PairedReturnGraphIntersection.M.map q :=
    (imageDelta Q q).subtype wsmall.head
  refine ⟨small, smallHead, ?_, wsmall.head.property, ?_⟩
  · dsimp [small, smallHead]
    exact hcompare
  · intro x hx
    have hrange :=
      MatchedSubgroupAmalgamWordReflection.wordMap_letter_mem_range
        (MatchedSubgroupAmalgamWordReflection.IndexedMatched.factorInclusion
          (imageMatchedFactorSubgroup Q q))
        (fun _ ↦ Subtype.val_injective)
        wsmall.toWord x hx
    rcases x with ⟨b, x⟩
    cases b with
    | false =>
        obtain ⟨s, hs⟩ := hrange
        change imageRightSub Q q at s
        change (s : PairedReturnGraphIntersection.M.map q × Sync) = x at hs
        change x ∈ imageRightSub Q q
        rw [← hs]
        exact s.property

/-- Membership in the product of the mapped left vertex and mapped cutter
produces a target carry comparison whose syllables after the first lie in the
two mapped matched factor subgroups. -/
theorem exists_target_rightCarryComparison_of_map_leftRange_mul_mem
    (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    {d : PushoutI.NormalWord.Transversal
      (Amalgam.famHom edgeToP edgeToC)}
    (w : PushoutI.NormalWord d)
    (hred : PushoutI.Reduced
      (Amalgam.famHom edgeToP edgeToC) w.toWord)
    (hedge : ∀ g ∈ leftFactors w.toWord.toList,
      q g ∉ PairedReturnGraphIntersection.M.map q)
    (hinter : Star.graphSub.map q ⊓
        PairedReturnGraphIntersection.M.map q =
      PairedReturnGraphIntersection.deltaSub.map q)
    (hmem : ambientToImageLamp Q q w.prod ∈
      (leftRange.map (ambientToImageLamp Q q) :
          Set (FreeLamp Q
            (PairedReturnGraphIntersection.M.map q) Sync)) *
        (matchedCutter.map (ambientToImageLamp Q q) : Set _)) :
    ∃ (small : List (Σ b,
          LampFactor Q (PairedReturnGraphIntersection.M.map q) Sync b))
      (smallHead : PairedReturnGraphIntersection.M.map q),
      MatchedSubgroupAmalgamWordReflection.RightCarryComparison
        (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
        (quotientWord Q q w.toWord hred hedge).toList small
        ((edgeToImage Q q w.head)⁻¹ * smallHead) ∧
      ∀ x ∈ small.tail,
        x.2 ∈ imageMatchedFactorSubgroup Q q x.1 := by
  obtain ⟨a, ha, l, hl, hal⟩ := hmem
  obtain ⟨a₀, ⟨g, rfl⟩, rfl⟩ := Subgroup.mem_map.mp ha
  have hlrange : l ∈
      (MatchedSubgroupAmalgamWordReflection.IndexedMatched.matchedMap
        (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
        (imageMatchedFactorSubgroup Q q) (imageDelta Q q)
        (imageMatchedFactorSubgroup_comap_edge Q q hinter)).range := by
    rw [← map_matchedCutter_eq_imageMatchedMap_range Q q hinter]
    exact hl
  obtain ⟨y, hy⟩ := hlrange
  apply
    MatchedSubgroupAmalgamWordReflection.IndexedMatched.exists_rightCarryComparison_of_eq_factor_mul_matchedMap
      (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
      (imageMatchedFactorSubgroup Q q) (imageDelta Q q)
      (lampMap_injective Q (PairedReturnGraphIntersection.M.map q) Sync)
      (imageMatchedFactorSubgroup_comap_edge Q q hinter)
      (quotientWord Q q w.toWord hred hedge)
      (quotientWord_reduced Q q w.toWord hred hedge)
      (edgeToImage Q q w.head) true (q g) y
  calc
    PushoutI.base
          (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
          (edgeToImage Q q w.head) *
        PushoutI.ofCoprodI
          (quotientWord Q q w.toWord hred hedge).prod =
      ambientToImageLamp Q q w.prod :=
        (ambientToImageLamp_normalWord_prod Q q w hred hedge).symm
    _ = ambientToImageLamp Q q
          (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC g) * l := hal.symm
    _ = PushoutI.of
          (φ := lampMap Q
            (PairedReturnGraphIntersection.M.map q) Sync) true (q g) *
        MatchedSubgroupAmalgamWordReflection.IndexedMatched.matchedMap
          (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
          (imageMatchedFactorSubgroup Q q) (imageDelta Q q)
          (imageMatchedFactorSubgroup_comap_edge Q q hinter) y := by
      rw [ambientToImageLamp_left, hy]
    | true =>
        obtain ⟨s, hs⟩ := hrange
        change Star.graphSub.map q at s
        change (s : Q) = x at hs
        change x ∈ Star.graphSub.map q
        rw [← hs]
        exact s.property

/-- Every excluded element has a reduced normal spelling and a finite refined
quotient preserving its right-scan obstruction with exact mapped edge
intersection. -/
theorem exists_finite_refinement_preserving_rightObstruction
    {z : Ambient} (hz : z ∉ matchedCutter) :
    ∃ (d : PushoutI.NormalWord.Transversal
          (Amalgam.famHom edgeToP edgeToC))
      (w : PushoutI.NormalWord d)
      (Q : Type) (_ : Group Q) (_ : Finite Q)
      (q : PairedReturnGraphIntersection.P →* Q),
      w.prod = z ∧ w.prod ∉ matchedCutter ∧
      RightPreservedObstruction Q q w ∧
      Star.graphSub.map q ⊓ PairedReturnGraphIntersection.M.map q =
        PairedReturnGraphIntersection.deltaSub.map q := by
  classical
  letI : ∀ b : Bool,
      DecidableEq (Amalgam.fam PairedReturnGraphIntersection.P C b) :=
    fun _ ↦ Classical.decEq _
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty
    (Amalgam.famHom edgeToP edgeToC)
    (Amalgam.famHom_injective edgeToP edgeToC
      edgeToP_injective edgeToC_injective)
  let w : PushoutI.NormalWord d := PushoutI.NormalWord.equiv z
  have hwprod : w.prod = z :=
    (PushoutI.NormalWord.equiv (d := d)).symm_apply_apply z
  have hwout : w.prod ∉ matchedCutter := by rwa [hwprod]
  have hedge := leftFactors_not_mem_edge w
  rcases exists_rightBad_or_terminal_of_normalWord_not_mem w hwout with
      hbad | hterminal
  · obtain ⟨pre, g, rest, tail, hlist, hscan, hfail⟩ := hbad
    have hinv : (g * (tail : PairedReturnGraphIntersection.P))⁻¹ ∉
        LeftProduct := by
      intro hmem
      obtain ⟨a, ha, m, hm, ham⟩ := hmem
      apply hfail
      refine ⟨m⁻¹, PairedReturnGraphIntersection.M.inv_mem hm,
        a⁻¹, Star.graphSub.inv_mem ha, ?_⟩
      have hinvEq := congrArg Inv.inv ham
      simpa using hinvEq
    obtain ⟨Q₀, hQgroup, hQfinite, q₀, hleft, _, hedge₀⟩ :=
      exists_finite_hom_reflecting_obstruction_lists
        [(g * (tail : PairedReturnGraphIntersection.P))⁻¹] []
        (leftFactors w.toWord.toList) (by
          intro x hx
          rw [List.mem_singleton] at hx
          subst x
          exact hinv) (by simp) hedge
    letI : Group Q₀ := hQgroup
    letI : Finite Q₀ := hQfinite
    let q :=
      PairedReturnImageIntersectionRefinement.refineHom Q₀ q₀
    letI : Group
        (PairedReturnImageIntersectionRefinement.Target Q₀ q₀) :=
      inferInstance
    letI : Finite
        (PairedReturnImageIntersectionRefinement.Target Q₀ q₀) :=
      inferInstance
    refine ⟨d, w, _, inferInstance, inferInstance, q,
      hwprod, hwout, ?_, ?_⟩
    · constructor
      · left
        refine ⟨pre, g, rest, tail, hlist, hscan, ?_⟩
        intro hmem
        obtain ⟨a, ha, m, hm, ham⟩ := hmem
        obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
        obtain ⟨m₀, hm₀, rfl⟩ := Subgroup.mem_map.mp hm
        apply hleft ((g * (tail : PairedReturnGraphIntersection.P))⁻¹) (by simp)
        refine ⟨q₀ a₀, ⟨a₀, ha₀, rfl⟩,
          q₀ m₀, ⟨m₀, hm₀, rfl⟩, ?_⟩
        exact congrArg Prod.fst ham
      · intro x hx hmem
        obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hmem
        apply hedge₀ x hx
        exact ⟨m, hm, congrArg Prod.fst hmx⟩
    · exact
        PairedReturnImageIntersectionRefinement.map_graph_inf_map_edge_eq_map_delta
          Q₀ q₀
  · obtain ⟨head, hscan, hfail⟩ := hterminal
    let terminal :=
      (w.head : PairedReturnGraphIntersection.P) * (head : _)
    obtain ⟨Q₀, hQgroup, hQfinite, q₀, _, hgraph, hedge₀⟩ :=
      exists_finite_hom_reflecting_obstruction_lists [] [terminal]
        (leftFactors w.toWord.toList) (by simp) (by
          intro x hx
          rw [List.mem_singleton] at hx
          subst x
          exact hfail) hedge
    letI : Group Q₀ := hQgroup
    letI : Finite Q₀ := hQfinite
    let q :=
      PairedReturnImageIntersectionRefinement.refineHom Q₀ q₀
    letI : Group
        (PairedReturnImageIntersectionRefinement.Target Q₀ q₀) :=
      inferInstance
    letI : Finite
        (PairedReturnImageIntersectionRefinement.Target Q₀ q₀) :=
      inferInstance
    refine ⟨d, w, _, inferInstance, inferInstance, q,
      hwprod, hwout, ?_, ?_⟩
    · constructor
      · right
        refine ⟨head, hscan, ?_⟩
        intro hmem
        obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hmem
        apply hgraph terminal (by simp)
        exact ⟨a, ha, congrArg Prod.fst hax⟩
      · intro x hx hmem
        obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hmem
        apply hedge₀ x hx
        exact ⟨m, hm, congrArg Prod.fst hmx⟩
    · exact
        PairedReturnImageIntersectionRefinement.map_graph_inf_map_edge_eq_map_delta
          Q₀ q₀

/-- A preserved right obstruction rejects membership in the mapped cutter.
The two carry comparisons have the same literal quotient word.  Exact mapped
edge intersection forces their carries to differ in the mapped returning
subgroup, which contradicts either the displayed bad left syllable or the
terminal graph obstruction. -/
theorem not_mem_map_matchedCutter_of_rightPreservedObstruction
    (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    {d : PushoutI.NormalWord.Transversal
      (Amalgam.famHom edgeToP edgeToC)}
    (w : PushoutI.NormalWord d)
    (hinter : Star.graphSub.map q ⊓
        PairedReturnGraphIntersection.M.map q =
      PairedReturnGraphIntersection.deltaSub.map q)
    (hpres : RightPreservedObstruction Q q w) :
    ambientToImageLamp Q q w.prod ∉
      matchedCutter.map (ambientToImageLamp Q q) := by
  classical
  have hred := PushoutEmbedding.normalWord_reduced
    (Amalgam.famHom edgeToP edgeToC) d w
  have hedge := hpres.2
  intro hmem
  obtain ⟨small, smallHead, htarget, hsmallHead, hsmall⟩ :=
    exists_target_rightCarryComparison_of_map_mem Q q w hred hedge hinter hmem
  have hcomap := imageMatchedFactorSubgroup_comap_edge Q q hinter
  rcases hpres.1 with hbad | hterminal
  · obtain ⟨pre, g, rest, tail, hlist, hscan, hout⟩ := hbad
    obtain ⟨sourceSmall, hsource, hsourceSmall⟩ :=
      exists_image_rightCarryComparison_of_rightEdgeScan Q q hscan
    have hquotientList :
        (quotientWord Q q w.toWord hred hedge).toList =
          pre.map (quotientLetter Q q) ++
            ⟨true, q g⟩ :: rest.map (quotientLetter Q q) := by
      change w.toWord.toList.map (quotientLetter Q q) = _
      rw [hlist, List.map_append]
      rfl
    rw [hquotientList] at htarget
    obtain ⟨smallPre, s, smallRest, current, targetTail,
        hsmallEq, heq, htargetRest⟩ :=
      MatchedSubgroupAmalgamWordReflection.RightCarryComparison.exists_at_append
          (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync) htarget
    change Q at s
    have hs : s ∈ Star.graphSub.map q := by
      have hs' : (⟨true, s⟩ : Σ b,
          LampFactor Q (PairedReturnGraphIntersection.M.map q) Sync b).2 ∈
          imageMatchedFactorSubgroup Q q true := by
        exact hsmall ⟨true, s⟩ (by
        rw [hsmallEq]
        exact List.mem_append.mpr
          (Or.inr (List.mem_cons_self)))
      exact hs'
    have hsmallRest : ∀ x ∈ smallRest,
        x.2 ∈ imageMatchedFactorSubgroup Q q x.1 := by
      intro x hx
      apply hsmall x
      rw [hsmallEq]
      exact List.mem_append.mpr
        (Or.inr (List.mem_cons_of_mem _ hx))
    have hdelta :
        (edgeToImage Q q tail)⁻¹ * targetTail ∈ imageDelta Q q :=
      MatchedSubgroupAmalgamWordReflection.RightCarryComparison.head_div_mem
        (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
        (imageMatchedFactorSubgroup Q q) (imageDelta Q q) hcomap
        hsource htargetRest hsourceSmall hsmallRest
    have hdeltaGraph :
        ((edgeToImage Q q tail)⁻¹ * targetTail :
          PairedReturnGraphIntersection.M.map q) ∈
            (Star.graphSub.map q).comap
              (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync true) := by
      rw [imageGraph_comap_edge_eq_imageDelta Q q hinter]
      exact hdelta
    apply hout
    refine ⟨
      (((edgeToImage Q q tail)⁻¹ * targetTail :
          PairedReturnGraphIntersection.M.map q) : Q) * s⁻¹,
      (Star.graphSub.map q).mul_mem hdeltaGraph
        ((Star.graphSub.map q).inv_mem hs),
      ((current : PairedReturnGraphIntersection.M.map q) : Q)⁻¹,
      (PairedReturnGraphIntersection.M.map q).inv_mem current.property, ?_⟩
    change q g * (targetTail : Q) =
      (current : Q) * (show Q from s) at heq
    change (((edgeToImage Q q tail :
        PairedReturnGraphIntersection.M.map q) : Q)⁻¹ *
        (targetTail : Q)) * s⁻¹ * (current : Q)⁻¹ = _
    have hedgeq : (((edgeToImage Q q tail :
        PairedReturnGraphIntersection.M.map q) : Q)) =
        q (tail : PairedReturnGraphIntersection.P) := rfl
    have htailEq : (targetTail : Q) =
        (q g)⁻¹ * (current : Q) * s := by
      calc
        (targetTail : Q) = (q g)⁻¹ * (q g * (targetTail : Q)) := by group
        _ = (q g)⁻¹ * ((current : Q) * s) := by rw [heq]
        _ = (q g)⁻¹ * (current : Q) * s := by group
    rw [map_inv, map_mul, hedgeq, htailEq]
    group
  · obtain ⟨head, hscan, hout⟩ := hterminal
    obtain ⟨sourceSmall, hsource, hsourceSmall⟩ :=
      exists_image_rightCarryComparison_of_rightEdgeScan Q q hscan
    have hsource' :
        MatchedSubgroupAmalgamWordReflection.RightCarryComparison
          (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
          (quotientWord Q q w.toWord hred hedge).toList sourceSmall
          (edgeToImage Q q head) := by
      simpa [quotientWord] using hsource
    have hdelta : (edgeToImage Q q head)⁻¹ *
          ((edgeToImage Q q w.head)⁻¹ * smallHead) ∈ imageDelta Q q :=
      MatchedSubgroupAmalgamWordReflection.RightCarryComparison.head_div_mem
        (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
        (imageMatchedFactorSubgroup Q q) (imageDelta Q q) hcomap
        hsource' htarget hsourceSmall hsmall
    have hdeltaGraph :
        ((edgeToImage Q q head)⁻¹ *
          ((edgeToImage Q q w.head)⁻¹ * smallHead) :
            PairedReturnGraphIntersection.M.map q) ∈
          (Star.graphSub.map q).comap
            (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync true) := by
      rw [imageGraph_comap_edge_eq_imageDelta Q q hinter]
      exact hdelta
    have hsmallHeadGraph : smallHead ∈
        (Star.graphSub.map q).comap
          (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync true) := by
      rw [imageGraph_comap_edge_eq_imageDelta Q q hinter]
      exact hsmallHead
    apply hout
    have hprodGraph := (Star.graphSub.map q).mul_mem hsmallHeadGraph
      ((Star.graphSub.map q).inv_mem hdeltaGraph)
    convert hprodGraph using 1
    rw [map_mul]
    change q (w.head : PairedReturnGraphIntersection.P) *
        q (head : PairedReturnGraphIntersection.P) =
      (smallHead : Q) *
        ((q (head : PairedReturnGraphIntersection.P))⁻¹ *
          ((q (w.head : PairedReturnGraphIntersection.P))⁻¹ *
            (smallHead : Q)))⁻¹
    group
/-- The same quotient in the iterated-central-HNN model used by the finite
free-label action. -/
def ambientToFiniteStage2 (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) :
    Ambient →* FreeLampFinitePresentation.Stage2 Q
      (PairedReturnGraphIntersection.M.map q) :=
  (FreeLampFinitePresentation.toStage2 Q
      (PairedReturnGraphIntersection.M.map q)).comp
    ((FreeLampFinitePresentation.freeLampMap Q
      (PairedReturnGraphIntersection.M.map q) syncEquivFree).comp
        (ambientToImageLamp Q q))

@[simp] theorem ambientToFiniteStage2_left (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    (g : PairedReturnGraphIntersection.P) :
    ambientToFiniteStage2 Q q
        (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC g) =
      FreeLampFinitePresentation.baseToStage2 Q
        (PairedReturnGraphIntersection.M.map q) (q g) := by
  change FreeLampFinitePresentation.toStage2 Q
      (PairedReturnGraphIntersection.M.map q)
      (FreeLampFinitePresentation.freeLampMap Q
        (PairedReturnGraphIntersection.M.map q) syncEquivFree
        (ambientToImageLamp Q q
          (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC g))) = _
  rw [ambientToImageLamp_left,
    FreeLampFinitePresentation.freeLampMap_inAmbient,
    FreeLampFinitePresentation.toStage2_inAmbient]

@[simp] theorem ambientToFiniteStage2_rightLamp (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) (s : Sync) :
    ambientToFiniteStage2 Q q
        (MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (1, s)) =
      FreeLampFinitePresentation.freeToStage2 Q
        (PairedReturnGraphIntersection.M.map q) (syncEquivFree s) := by
  change FreeLampFinitePresentation.toStage2 Q
      (PairedReturnGraphIntersection.M.map q)
      (FreeLampFinitePresentation.freeLampMap Q
        (PairedReturnGraphIntersection.M.map q) syncEquivFree
        (ambientToImageLamp Q q
          (MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (1, s)))) = _
  rw [ambientToImageLamp_right_eq]
  simp only [map_one, one_mul,
    FreeLampFinitePresentation.freeLampMap_inLamp]
  induction (syncEquivFree s) using FreeGroup.induction_on with
  | C1 =>
      rw [map_one, map_one]
      exact (map_one (FreeLampFinitePresentation.freeToStage2 Q
        (PairedReturnGraphIntersection.M.map q))).symm
  | of i =>
      simpa [FreeLampFinitePresentation.freeToStage2] using
        FreeLampFinitePresentation.toStage2_inLamp_of Q
          (PairedReturnGraphIntersection.M.map q) i
  | mul x y hx hy =>
      simp only [map_mul, hx, hy]
  | inv_of i hi =>
      simp only [map_inv, hi]

theorem ambientToFiniteStage2_right_eq (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q) (m : Edge) (s : Sync) :
    ambientToFiniteStage2 Q q
        (MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (m, s)) =
      FreeLampFinitePresentation.baseToStage2 Q
          (PairedReturnGraphIntersection.M.map q) (q (edgeToP m)) *
        FreeLampFinitePresentation.freeToStage2 Q
          (PairedReturnGraphIntersection.M.map q) (syncEquivFree s) := by
  have hsource :
      MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (m, s) =
        MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (m, 1) *
          MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (1, s) := by
    rw [← map_mul]
    simp
  rw [hsource, map_mul, ambientToFiniteStage2_rightLamp]
  have hedge :
      MatchedSubgroupAmalgam.bigInB edgeToP edgeToC (m, 1) =
        MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (edgeToP m) :=
    (PushoutI.of_apply_eq_base (Amalgam.famHom edgeToP edgeToC) true m).trans
      (PushoutI.of_apply_eq_base (Amalgam.famHom edgeToP edgeToC) false m).symm
  rw [hedge, ambientToFiniteStage2_left]

/-- Every finitely generated subgroup of the finite-base quotient free lamp
is profinitely closed. -/
theorem imageLamp_profiniteClosure_eq_of_fg
    (Q : Type) [Group Q] [Finite Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    (H : Subgroup
      (FreeLamp Q (PairedReturnGraphIntersection.M.map q) Sync))
    (hH : H.FG) :
    profiniteClosure H = H := by
  obtain ⟨d⟩ := HNNExtension.NormalWord.TransversalPair.nonempty Q
    (PairedReturnGraphIntersection.M.map q)
    (PairedReturnGraphIntersection.M.map q)
  exact FreeLampFiniteBaseProfinite.profiniteClosure_eq_of_fg_of_lampEquiv
    (M := PairedReturnGraphIntersection.M.map q) d syncEquivFree H hH

/-- The image of the concrete matched cutter is closed in every finite-base
free-lamp quotient. -/
theorem profiniteClosure_map_matchedCutter
    (Q : Type) [Group Q] [Finite Q]
    (q : PairedReturnGraphIntersection.P →* Q) :
    profiniteClosure
        (matchedCutter.map (ambientToImageLamp Q q)) =
      matchedCutter.map (ambientToImageLamp Q q) := by
  apply imageLamp_profiniteClosure_eq_of_fg Q q
  apply Higman.fg_map
  rw [← fiveCutter_eq_matchedCutter]
  exact fiveCutter_fg

/-- Closure membership in the original ambient becomes actual cutter
membership after every finite-base free-lamp quotient. -/
theorem image_mem_map_matchedCutter_of_mem_profiniteClosure
    (Q : Type) [Group Q] [Finite Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    {z : Ambient} (hz : z ∈ profiniteClosure matchedCutter) :
    ambientToImageLamp Q q z ∈
      matchedCutter.map (ambientToImageLamp Q q) := by
  have hImageClosure : ambientToImageLamp Q q z ∈
      profiniteClosure (matchedCutter.map (ambientToImageLamp Q q)) := by
    intro R _ _ r
    have h := hz R (r.comp (ambientToImageLamp Q q))
    rwa [Subgroup.map_map]
  rwa [profiniteClosure_map_matchedCutter Q q] at hImageClosure

/-- Once an element survives outside the mapped cutter in one finite-base
free lamp, finite-base LERF supplies an actual finite separating quotient. -/
theorem not_mem_profiniteClosure_matchedCutter_of_image
    (Q : Type) [Group Q] [Finite Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    {z : Ambient}
    (hz : ambientToImageLamp Q q z ∉
      matchedCutter.map (ambientToImageLamp Q q)) :
    z ∉ profiniteClosure matchedCutter := by
  have hzTarget : ambientToImageLamp Q q z ∉
      profiniteClosure (matchedCutter.map (ambientToImageLamp Q q)) := by
    rwa [profiniteClosure_map_matchedCutter Q q]
  intro hzClosure
  apply hzTarget
  intro R _ _ r
  have h := hzClosure R (r.comp (ambientToImageLamp Q q))
  rwa [Subgroup.map_map]

/-- The concrete matched cutter is profinitely closed. -/
theorem profiniteClosure_matchedCutter :
    profiniteClosure matchedCutter = matchedCutter := by
  apply le_antisymm
  · intro z hz
    by_contra hout
    obtain ⟨d, w, Q, hQgroup, hQfinite, q,
        hwprod, -, hpres, hinter⟩ :=
      exists_finite_refinement_preserving_rightObstruction hout
    letI : Group Q := hQgroup
    letI : Finite Q := hQfinite
    have hImage : ambientToImageLamp Q q z ∉
        matchedCutter.map (ambientToImageLamp Q q) := by
      rw [← hwprod]
      exact not_mem_map_matchedCutter_of_rightPreservedObstruction
        Q q w hinter hpres
    exact (not_mem_profiniteClosure_matchedCutter_of_image Q q hImage) hz
  · exact le_profiniteClosure matchedCutter

/-- The original five-generator paired-return cutter is profinitely closed. -/
theorem profiniteClosure_fiveCutter :
    profiniteClosure fiveCutter = fiveCutter := by
  rw [fiveCutter_eq_matchedCutter]
  exact profiniteClosure_matchedCutter

/-- A finite list of points outside a closed subgroup can be kept outside
simultaneously in one finite product quotient. -/
theorem exists_finite_hom_reflecting_list_of_closed
    {G : Type} [Group G] (H : Subgroup G)
    (hclosed : profiniteClosure H = H) :
    ∀ l : List G, (∀ x ∈ l, x ∉ H) →
      ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (q : G →* Q),
        ∀ x ∈ l, q x ∉ H.map q
  | [] => by
      intro _
      exact ⟨PUnit, inferInstance, inferInstance, 1, by simp⟩
  | x :: l => by
      intro hout
      have hxClosure : x ∉ profiniteClosure H := by
        rw [hclosed]
        exact hout x List.mem_cons_self
      have hxSep : ∃ (Q : Type) (_ : Group Q) (_ : Finite Q)
          (q : G →* Q), q x ∉ H.map q := by
        by_contra hnone
        apply hxClosure
        intro Q _ _ q
        by_contra hq
        apply hnone
        exact ⟨Q, inferInstance, inferInstance, q, hq⟩
      obtain ⟨Q, hQgroup, hQfinite, q, hqx⟩ := hxSep
      letI : Group Q := hQgroup
      letI : Finite Q := hQfinite
      obtain ⟨R, hRgroup, hRfinite, r, hr⟩ :=
        exists_finite_hom_reflecting_list_of_closed H hclosed l
          (fun y hy ↦ hout y (List.mem_cons_of_mem x hy))
      letI : Group R := hRgroup
      letI : Finite R := hRfinite
      refine ⟨Q × R, inferInstance, inferInstance, q.prod r, ?_⟩
      intro y hy hmem
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hmem
      rcases List.mem_cons.mp hy with rfl | hy
      · apply hqx
        exact ⟨z, hz, congrArg Prod.fst hzy⟩
      · apply hr y hy
        exact ⟨z, hz, congrArg Prod.snd hzy⟩

/-- In an exact-intersection image free lamp, membership of a displayed base
element in the mapped cutter reflects membership in the mapped graph. -/
theorem imageLamp_left_mem_map_matchedCutter_iff
    (Q : Type) [Group Q]
    (q : PairedReturnGraphIntersection.P →* Q)
    (hinter : Star.graphSub.map q ⊓
        PairedReturnGraphIntersection.M.map q =
      PairedReturnGraphIntersection.deltaSub.map q)
    (g : Q) :
    inAmbient Q (PairedReturnGraphIntersection.M.map q) Sync g ∈
        matchedCutter.map (ambientToImageLamp Q q) ↔
      g ∈ Star.graphSub.map q := by
  constructor
  · intro hg
    rw [map_matchedCutter_eq_imageMatchedMap_range Q q hinter] at hg
    obtain ⟨y, hy⟩ := hg
    have hyFactor :
        MatchedSubgroupAmalgamWordReflection.IndexedMatched.matchedMap
            (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
            (imageMatchedFactorSubgroup Q q) (imageDelta Q q)
            (imageMatchedFactorSubgroup_comap_edge Q q hinter) y ∈
          (PushoutI.of
            (φ := lampMap Q
              (PairedReturnGraphIntersection.M.map q) Sync) true).range := by
      rw [hy]
      exact ⟨g, rfl⟩
    obtain ⟨s, hs⟩ :=
      MatchedSubgroupAmalgamWordReflection.IndexedMatched.matchedMap_reflects_factor_range
          (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
          (imageMatchedFactorSubgroup Q q) (imageDelta Q q)
          (lampMap_injective Q
            (PairedReturnGraphIntersection.M.map q) Sync)
          (imageMatchedFactorSubgroup_comap_edge Q q hinter) true y hyFactor
    change Star.graphSub.map q at s
    have hmap :=
      MatchedSubgroupAmalgamWordReflection.IndexedMatched.matchedMap_of
        (lampMap Q (PairedReturnGraphIntersection.M.map q) Sync)
        (imageMatchedFactorSubgroup Q q) (imageDelta Q q)
        (imageMatchedFactorSubgroup_comap_edge Q q hinter) true s
    rw [hs, hy] at hmap
    have hsg : (s : Q) = g :=
      (inAmbient_injective Q
        (PairedReturnGraphIntersection.M.map q) Sync) hmap.symm
    rw [← hsg]
    exact s.property
  · intro hg
    rw [map_matchedCutter_eq_imageGeneratorClosure]
    exact Subgroup.subset_closure
      (Or.inr ⟨g, hg, rfl⟩)

/-- Prescribed finite-quotient reflection for the concrete left embedding
and five-generator cutter. -/
theorem exists_finite_ambient_hom_factorization_reflecting
    (Q₀ : Type) [Group Q₀] [Finite Q₀]
    (q₀ : PairedReturnGraphIntersection.P →* Q₀) :
    ∃ (R : Type) (_ : Group R) (_ : Finite R) (p : Ambient →* R),
      ∀ g : PairedReturnGraphIntersection.P,
        p (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC g) ∈
            fiveCutter.map p →
          q₀ g ∈ Star.graphSub.map q₀ := by
  classical
  let q := PairedReturnImageIntersectionRefinement.refineHom Q₀ q₀
  let T := PairedReturnImageIntersectionRefinement.Target Q₀ q₀
  letI : Fintype T := Fintype.ofFinite T
  let L : Subgroup
      (FreeLamp T (PairedReturnGraphIntersection.M.map q) Sync) :=
    matchedCutter.map (ambientToImageLamp T q)
  let bad : List (FreeLamp T
      (PairedReturnGraphIntersection.M.map q) Sync) :=
    ((Finset.univ.filter fun a : T ↦
      a ∉ Star.graphSub.map q).image fun a ↦
        inAmbient T (PairedReturnGraphIntersection.M.map q) Sync a).toList
  have hinter : Star.graphSub.map q ⊓
      PairedReturnGraphIntersection.M.map q =
      PairedReturnGraphIntersection.deltaSub.map q :=
    PairedReturnImageIntersectionRefinement.map_graph_inf_map_edge_eq_map_delta Q₀ q₀
  have hbad : ∀ x ∈ bad, x ∉ L := by
    intro x hx
    rw [Finset.mem_toList] at hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have haout : a ∉ Star.graphSub.map q :=
      (Finset.mem_filter.mp ha).2
    exact fun hmem ↦ haout
      ((imageLamp_left_mem_map_matchedCutter_iff T q hinter a).mp hmem)
  have hLclosed : profiniteClosure L = L :=
    profiniteClosure_map_matchedCutter T q
  obtain ⟨R, hRgroup, hRfinite, r, hr⟩ :=
    exists_finite_hom_reflecting_list_of_closed L hLclosed bad hbad
  refine ⟨R, hRgroup, hRfinite,
    r.comp (ambientToImageLamp T q), ?_⟩
  intro g hmem
  by_contra hq₀
  have hq : q g ∉ Star.graphSub.map q := by
    rintro ⟨a, ha, haq⟩
    apply hq₀
    exact ⟨a, ha, congrArg Prod.fst haq⟩
  have hbadmem : inAmbient T
      (PairedReturnGraphIntersection.M.map q) Sync (q g) ∈ bad := by
    rw [Finset.mem_toList]
    apply Finset.mem_image.mpr
    exact ⟨q g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩, rfl⟩
  apply hr _ hbadmem
  change r (ambientToImageLamp T q
      (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC g)) ∈
    fiveCutter.map (r.comp (ambientToImageLamp T q)) at hmem
  rw [ambientToImageLamp_left, fiveCutter_eq_matchedCutter,
    ← Subgroup.map_map] at hmem
  exact hmem

end PairedReturnMatchedCutterProfinite
end Higman
end GroupApproximation
