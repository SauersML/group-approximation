import GroupApproximation.Kazhdan.CCKWTitsPresentation
import GroupApproximation.Kazhdan.CCKWCosetComplex
import GroupApproximation.Meta.AxiomGuard

/-!
# The coset complex of `GHB(7)` is simply connected

`GHB(7) = ⟨a, b, c⟩` with eleven relators, and its vertex groups are `P₀ = ⟨a, b⟩`,
`P₁ = ⟨c, b⟩`, `P₂ = ⟨c, a⟩` (`KMSGroup.vertexGroup`).  Every relator is a word in the generators
of one vertex group: `a⁷`, `b⁷` and the four-letter and five-letter commutators in `a, b` lie in
`P₀`; `c⁷` and the commutators in `c, b` lie in `P₁`; the commutators in `c, a` lie in `P₂`
(`relator_mem_closure`).  So the presentation is a vertex presentation (`ghbVertexPresentation`)
and Tits' lemma (`Kazhdan/CCKWTitsPresentation.lean`) makes the coset complex
`KMSGroup.CCKW.cosetComplex` simply connected and connected.
-/

namespace GroupApproximation.CCKWTits

open KMSGroup

/-- The generator types: `a ↦ P₀`, `b ↦ P₀`, `c ↦ P₁`. -/
def ghbτ : Fin 3 → Fin 3 := ![0, 0, 1]

/-- The generators of the vertex groups. -/
def ghbStype : Fin 3 → Set (Fin 3) := ![{0, 1}, {2, 1}, {2, 0}]

theorem vertexGroup_zero :
    vertexGroup 0 = (Subgroup.closure (FreeGroup.of '' ghbStype 0)).map (PresentedGroup.mk (relators 7)) := by
  show Subgroup.closure {a 7, b 7} =
    (Subgroup.closure (FreeGroup.of '' ({0, 1} : Set (Fin 3)))).map (PresentedGroup.mk (relators 7))
  rw [MonoidHom.map_closure, Set.image_image, Set.image_insert_eq, Set.image_singleton]
  rfl

theorem vertexGroup_one :
    vertexGroup 1 = (Subgroup.closure (FreeGroup.of '' ghbStype 1)).map (PresentedGroup.mk (relators 7)) := by
  show Subgroup.closure {c 7, b 7} =
    (Subgroup.closure (FreeGroup.of '' ({2, 1} : Set (Fin 3)))).map (PresentedGroup.mk (relators 7))
  rw [MonoidHom.map_closure, Set.image_image, Set.image_insert_eq, Set.image_singleton]
  rfl

theorem vertexGroup_two :
    vertexGroup 2 = (Subgroup.closure (FreeGroup.of '' ghbStype 2)).map (PresentedGroup.mk (relators 7)) := by
  show Subgroup.closure {c 7, a 7} =
    (Subgroup.closure (FreeGroup.of '' ({2, 0} : Set (Fin 3)))).map (PresentedGroup.mk (relators 7))
  rw [MonoidHom.map_closure, Set.image_image, Set.image_insert_eq, Set.image_singleton]
  rfl

theorem comm_mem {G : Type*} [Group G] {K : Subgroup G} {x y : G} (hx : x ∈ K) (hy : y ∈ K) :
    KMSGroup.comm x y ∈ K :=
  mul_mem (mul_mem (mul_mem (inv_mem hx) (inv_mem hy)) hx) hy

theorem comm3_mem {G : Type*} [Group G] {K : Subgroup G} {x y z : G} (hx : x ∈ K) (hy : y ∈ K)
    (hz : z ∈ K) : KMSGroup.comm3 x y z ∈ K :=
  comm_mem (comm_mem hx hy) hz

theorem comm4_mem {G : Type*} [Group G] {K : Subgroup G} {x y z w : G} (hx : x ∈ K) (hy : y ∈ K)
    (hz : z ∈ K) (hw : w ∈ K) : KMSGroup.comm4 x y z w ∈ K :=
  comm_mem (comm3_mem hx hy hz) hw

theorem gen_mem_closure {j : Fin 3} {s : Fin 3} (hs : s ∈ ghbStype j) :
    (FreeGroup.of s : FreeGroup (Fin 3)) ∈ Subgroup.closure (FreeGroup.of '' ghbStype j) :=
  Subgroup.subset_closure ⟨s, hs, rfl⟩

/-- **Every relator of `GHB(7)` is a word in the generators of one vertex group.** -/
theorem relator_mem_closure (r : FreeGroup (Fin 3)) (hr : r ∈ relators 7) :
    ∃ j, r ∈ Subgroup.closure (FreeGroup.of '' ghbStype j) := by
  have hr' : r ∈ relatorList 7 := List.mem_toFinset.mp (Finset.mem_coe.mp hr)
  have a0 : ga ∈ Subgroup.closure (FreeGroup.of '' ghbStype 0) :=
    gen_mem_closure (Set.mem_insert _ _)
  have b0 : gb ∈ Subgroup.closure (FreeGroup.of '' ghbStype 0) :=
    gen_mem_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have c1 : gc ∈ Subgroup.closure (FreeGroup.of '' ghbStype 1) :=
    gen_mem_closure (Set.mem_insert _ _)
  have b1 : gb ∈ Subgroup.closure (FreeGroup.of '' ghbStype 1) :=
    gen_mem_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have c2 : gc ∈ Subgroup.closure (FreeGroup.of '' ghbStype 2) :=
    gen_mem_closure (Set.mem_insert _ _)
  have a2 : ga ∈ Subgroup.closure (FreeGroup.of '' ghbStype 2) :=
    gen_mem_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  simp only [relatorList, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, pow_mem a0 7⟩
  · exact ⟨0, pow_mem b0 7⟩
  · exact ⟨1, pow_mem c1 7⟩
  · exact ⟨0, comm3_mem a0 b0 a0⟩
  · exact ⟨0, comm3_mem a0 b0 b0⟩
  · exact ⟨1, comm3_mem c1 b1 c1⟩
  · exact ⟨1, comm4_mem c1 b1 b1 c1⟩
  · exact ⟨1, comm4_mem c1 b1 b1 b1⟩
  · exact ⟨2, comm3_mem c2 a2 c2⟩
  · exact ⟨2, comm4_mem c2 a2 a2 c2⟩
  · exact ⟨2, comm4_mem c2 a2 a2 a2⟩

/-- **`GHB(7)` is a vertex presentation for its three vertex groups.** -/
def ghbVertexPresentation : VertexPresentation (relators 7) vertexGroup where
  Stype := ghbStype
  τ := ghbτ
  hH := by
    intro i
    fin_cases i
    · exact vertexGroup_zero
    · exact vertexGroup_one
    · exact vertexGroup_two
  hτ := by
    intro s
    fin_cases s
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl
    · exact Set.mem_insert _ _
  hR := relator_mem_closure

/-- **The coset complex of `GHB(7)` is simply connected** (CCKW T2, Tits' lemma). -/
theorem cckwCosetComplex_simplyConnected : Systolic.SimplyConnected CCKW.cosetComplex :=
  simplyConnected_of_vertexPresentation ghbVertexPresentation

/-- **The coset complex of `GHB(7)` is connected.** -/
theorem cckwCosetComplex_connected : CCKW.cosetComplex.G.Connected :=
  connected_of_vertexPresentation ghbVertexPresentation

end GroupApproximation.CCKWTits

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CCKWTits.relator_mem_closure
#audit_closed_axioms GroupApproximation.CCKWTits.cckwCosetComplex_simplyConnected
#audit_closed_axioms GroupApproximation.CCKWTits.cckwCosetComplex_connected
