import GroupApproximation.Matching.FinitePartialBijection

/-!
# Partial bijections carried by biunique finite relations

A finite relation which is single-valued in both coordinates is exactly the
graph of a partial bijection.  This module constructs that partial bijection
without extending it outside the relation.  Keeping the construction partial
is essential when an invariant relation is used: an arbitrary completion to a
permutation need not retain invariance.
-/

namespace GroupApproximation
namespace FinitePartialBijection

variable {Y Z : FiniteModel}

/-- The first-coordinate support of a finite relation. -/
def relationSource (R : Finset (Y × Z)) : Finset Y :=
  R.image Prod.fst

/-- The second-coordinate support of a finite relation. -/
def relationTarget (R : Finset (Y × Z)) : Finset Z :=
  R.image Prod.snd

@[simp] theorem mem_relationSource (R : Finset (Y × Z)) (y : Y) :
    y ∈ relationSource R ↔ ∃ z, (y, z) ∈ R := by
  simp [relationSource]

@[simp] theorem mem_relationTarget (R : Finset (Y × Z)) (z : Z) :
    z ∈ relationTarget R ↔ ∃ y, (y, z) ∈ R := by
  simp [relationTarget]

/-- The uniquely specified value of a relation at a supported source.
Uniqueness is not needed to define the value; it is used by the subsequent
constructor. -/
noncomputable def relationValue (R : Finset (Y × Z))
    (y : ↥(relationSource R)) : Z :=
  Classical.choose ((mem_relationSource R y.1).mp y.2)

theorem relationValue_mem (R : Finset (Y × Z))
    (y : ↥(relationSource R)) : (y.1, relationValue R y) ∈ R :=
  Classical.choose_spec ((mem_relationSource R y.1).mp y.2)

/-- Right uniqueness identifies every related value with the chosen one. -/
theorem relationValue_eq_of_mem (R : Finset (Y × Z))
    (hright : ∀ {y z w}, (y, z) ∈ R → (y, w) ∈ R → z = w)
    (y : ↥(relationSource R)) {z : Z} (hz : (y.1, z) ∈ R) :
    relationValue R y = z :=
  hright (relationValue_mem R y) hz

/-- A biunique finite relation, with no completion outside its supports,
viewed as a partial bijection. -/
noncomputable def ofBiuniqueRelation (R : Finset (Y × Z))
    (hright : ∀ {y z w}, (y, z) ∈ R → (y, w) ∈ R → z = w)
    (hleft : ∀ {y x z}, (y, z) ∈ R → (x, z) ∈ R → y = x) :
    FinitePartialBijection Y Z where
  source := relationSource R
  target := relationTarget R
  equiv := Equiv.ofBijective
    (fun y : ↥(relationSource R) ↦
      (⟨relationValue R y,
        (mem_relationTarget R (relationValue R y)).mpr
          ⟨y.1, relationValue_mem R y⟩⟩ : ↥(relationTarget R)))
    ⟨by
      intro y x h
      apply Subtype.ext
      have hv : relationValue R y = relationValue R x :=
        congrArg Subtype.val h
      apply hleft (relationValue_mem R y)
      simpa only [hv] using relationValue_mem R x,
     by
      intro z
      obtain ⟨y, hy⟩ := (mem_relationTarget R z.1).mp z.2
      have hySource : y ∈ relationSource R :=
        (mem_relationSource R y).mpr ⟨z.1, hy⟩
      let y' : ↥(relationSource R) := ⟨y, hySource⟩
      refine ⟨y', Subtype.ext ?_⟩
      exact relationValue_eq_of_mem R hright y' hy⟩

@[simp] theorem ofBiuniqueRelation_source (R : Finset (Y × Z))
    (hright : ∀ {y z w}, (y, z) ∈ R → (y, w) ∈ R → z = w)
    (hleft : ∀ {y x z}, (y, z) ∈ R → (x, z) ∈ R → y = x) :
    (ofBiuniqueRelation R hright hleft).source = relationSource R := rfl

@[simp] theorem ofBiuniqueRelation_target (R : Finset (Y × Z))
    (hright : ∀ {y z w}, (y, z) ∈ R → (y, w) ∈ R → z = w)
    (hleft : ∀ {y x z}, (y, z) ∈ R → (x, z) ∈ R → y = x) :
    (ofBiuniqueRelation R hright hleft).target = relationTarget R := rfl

@[simp] theorem ofBiuniqueRelation_apply (R : Finset (Y × Z))
    (hright : ∀ {y z w}, (y, z) ∈ R → (y, w) ∈ R → z = w)
    (hleft : ∀ {y x z}, (y, z) ∈ R → (x, z) ∈ R → y = x)
    (y : Y) (hy : y ∈ (ofBiuniqueRelation R hright hleft).source) :
    (ofBiuniqueRelation R hright hleft).apply y hy =
      relationValue R ⟨y, hy⟩ := rfl

/-- The graph of the constructed partial bijection is exactly the original
biunique relation. -/
theorem graph_ofBiuniqueRelation (R : Finset (Y × Z))
    (hright : ∀ {y z w}, (y, z) ∈ R → (y, w) ∈ R → z = w)
    (hleft : ∀ {y x z}, (y, z) ∈ R → (x, z) ∈ R → y = x) :
    (ofBiuniqueRelation R hright hleft).graph = R := by
  ext p
  rw [mem_graph]
  constructor
  · rintro ⟨hy, hp⟩
    have hchosen := relationValue_mem R
      (⟨p.1, hy⟩ : ↥(relationSource R))
    rw [ofBiuniqueRelation_apply] at hp
    rw [hp] at hchosen
    exact hchosen
  · intro hp
    have hy : p.1 ∈ relationSource R :=
      (mem_relationSource R p.1).mpr ⟨p.2, hp⟩
    refine ⟨hy, ?_⟩
    rw [ofBiuniqueRelation_apply]
    exact relationValue_eq_of_mem R hright ⟨p.1, hy⟩ hp

/-- Forward invariance of the graph makes the source invariant under the
source action. -/
theorem source_mapsTo_of_graph_mapsTo
    {G : Type*} [Group G]
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (hgraph : ∀ g y z, (y, z) ∈ b.graph →
      (σY g y, σZ g z) ∈ b.graph)
    (g : G) {y : Y} (hy : y ∈ b.source) : σY g y ∈ b.source := by
  have hmem : (y, b.apply y hy) ∈ b.graph :=
    (mem_graph b y (b.apply y hy)).mpr ⟨hy, rfl⟩
  have hmapped := hgraph g y (b.apply y hy) hmem
  exact (mem_graph b (σY g y) (σZ g (b.apply y hy))).mp hmapped |>.choose

/-- The same graph invariance makes the target invariant. -/
theorem target_mapsTo_of_graph_mapsTo
    {G : Type*} [Group G]
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (hgraph : ∀ g y z, (y, z) ∈ b.graph →
      (σY g y, σZ g z) ∈ b.graph)
    (g : G) {z : Z} (hz : z ∈ b.target) : σZ g z ∈ b.target := by
  let y := b.symm.apply z hz
  have hy : y ∈ b.source := b.symm.apply_mem_target z hz
  have hmem : (y, z) ∈ b.graph := by
    rw [mem_graph]
    exact ⟨hy, b.apply_symm_apply z hz⟩
  have hmapped := hgraph g y z hmem
  obtain ⟨hsource, heq⟩ :=
    (mem_graph b (σY g y) (σZ g z)).mp hmapped
  rw [← heq]
  exact b.apply_mem_target _ hsource

/-- A nonempty invariant source in a transitive action is the whole source
model. -/
theorem source_eq_univ_of_graph_mapsTo_of_transitive
    {G : Type*} [Group G]
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (hgraph : ∀ g y z, (y, z) ∈ b.graph →
      (σY g y, σZ g z) ∈ b.graph)
    (htrans : ∀ x y : Y, ∃ g : G, σY g x = y)
    (hne : b.source.Nonempty) : b.source = Finset.univ := by
  ext y
  simp only [Finset.mem_univ, iff_true]
  obtain ⟨x, hx⟩ := hne
  obtain ⟨g, hg⟩ := htrans x y
  rw [← hg]
  exact source_mapsTo_of_graph_mapsTo σY σZ b hgraph g hx

/-- A nonempty invariant target in a transitive action is the whole target
model. -/
theorem target_eq_univ_of_graph_mapsTo_of_transitive
    {G : Type*} [Group G]
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (hgraph : ∀ g y z, (y, z) ∈ b.graph →
      (σY g y, σZ g z) ∈ b.graph)
    (htrans : ∀ x y : Z, ∃ g : G, σZ g x = y)
    (hne : b.target.Nonempty) : b.target = Finset.univ := by
  ext z
  simp only [Finset.mem_univ, iff_true]
  obtain ⟨w, hw⟩ := hne
  obtain ⟨g, hg⟩ := htrans w z
  rw [← hg]
  exact target_mapsTo_of_graph_mapsTo σY σZ b hgraph g hw

/-- On its invariant graph, the partial bijection intertwines the two
actions exactly. -/
theorem apply_action_eq_of_graph_mapsTo
    {G : Type*} [Group G]
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (hgraph : ∀ g y z, (y, z) ∈ b.graph →
      (σY g y, σZ g z) ∈ b.graph)
    (g : G) (y : Y) (hy : y ∈ b.source)
    (hgy : σY g y ∈ b.source) :
    b.apply (σY g y) hgy = σZ g (b.apply y hy) := by
  have hmem : (y, b.apply y hy) ∈ b.graph :=
    (mem_graph b y (b.apply y hy)).mpr ⟨hy, rfl⟩
  have hmapped := hgraph g y (b.apply y hy) hmem
  obtain ⟨_, heq⟩ :=
    (mem_graph b (σY g y) (σZ g (b.apply y hy))).mp hmapped
  exact heq

/-- Swapping the coordinates of an invariant partial-bijection graph gives
the invariant graph of its inverse. -/
theorem symm_graph_mapsTo_of_graph_mapsTo
    {G : Type*} [Group G]
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (hgraph : ∀ g y z, (y, z) ∈ b.graph →
      (σY g y, σZ g z) ∈ b.graph)
    (g : G) (z : Z) (y : Y) (hzy : (z, y) ∈ b.symm.graph) :
    (σZ g z, σY g y) ∈ b.symm.graph := by
  obtain ⟨hz, heq⟩ := (mem_graph b.symm z y).mp hzy
  have hy : y ∈ b.source := by
    rw [← heq]
    exact b.symm.apply_mem_target z hz
  have hyz : (y, z) ∈ b.graph := by
    rw [mem_graph]
    refine ⟨hy, ?_⟩
    simpa only [heq, proof_irrel_heq] using b.apply_symm_apply z hz
  obtain ⟨hgy, hmap⟩ :=
    (mem_graph b (σY g y) (σZ g z)).mp (hgraph g y z hyz)
  rw [mem_graph]
  have htarget : σZ g z ∈ b.target := by
    rw [← hmap]
    exact b.apply_mem_target (σY g y) hgy
  refine ⟨htarget, ?_⟩
  have hinverse := b.symm_apply_apply (σY g y) hgy
  simpa only [hmap, proof_irrel_heq] using hinverse

/-- A full invariant graph has no labeled equivariance failures. -/
theorem equivarianceDefect_eq_empty_of_graph_mapsTo_of_source_eq_univ
    {L : Type*} [Fintype L]
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (hgraph : ∀ l y z, (y, z) ∈ b.graph →
      (actY l y, actZ l z) ∈ b.graph)
    (hsource : b.source = Finset.univ) :
    b.equivarianceDefect actY actZ = ∅ := by
  classical
  ext p
  simp only [equivarianceDefect, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.notMem_empty, iff_false]
  intro hdefect
  have hy : p.2 ∈ b.source := by rw [hsource]; exact Finset.mem_univ _
  have hsy : actY p.1 p.2 ∈ b.source := by
    rw [hsource]
    exact Finset.mem_univ _
  have hmem : (p.2, b.apply p.2 hy) ∈ b.graph :=
    (mem_graph b p.2 (b.apply p.2 hy)).mpr ⟨hy, rfl⟩
  obtain ⟨_, heq⟩ :=
    (mem_graph b (actY p.1 p.2) (actZ p.1 (b.apply p.2 hy))).mp
      (hgraph p.1 p.2 (b.apply p.2 hy) hmem)
  exact hdefect hy hsy heq

end FinitePartialBijection
end GroupApproximation
