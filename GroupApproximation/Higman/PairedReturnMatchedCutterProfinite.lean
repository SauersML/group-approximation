import GroupApproximation.Higman.PairedReturnLeftProductProfinite
import GroupApproximation.Higman.PairedReturnEdgeSeparable
import GroupApproximation.Higman.FreeLampFiniteBaseProfinite

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

end PairedReturnMatchedCutterProfinite
end Higman
end GroupApproximation
