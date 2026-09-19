import GroupApproximation.GGT.DGOTheorem442BBFBarrier
import GroupApproximation.GGT.DGOTheorem442CosetGraphMetric
import GroupApproximation.GGT.GuessingGeodesicsCriterion

/-!
# BBF standard walks as Bowditch guessing paths

At threshold `K >= 64 xi`, the BBF distance-two barrier theorem chooses a
standard walk between every pair of projection vertices.  For a coset graph,
representatives of its vertices lift that walk to the relative Cayley graph.
The lifted paths satisfy Bowditch's guessing-path conditions with constant six:
an adjacent-endpoint path has diameter at most six, and guessed triangles are
three-thin.

The final theorem lands in
`OsinEnlargement.guessingGeodesics`, the repository's proved form of Bowditch's
guessing-geodesics criterion.
-/

namespace GroupApproximation
namespace GGT
namespace ProjectionSystem

open GroupApproximation.WordMetric

universe u

variable {G : Type u} [Group G] {H : Subgroup G}

/-- A standard BBF walk, with the nil walk chosen when the endpoints agree. -/
noncomputable def chosenBBFWalk
    (P : ProjectionSystem (G ⧸ H)) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    (X Z : G ⧸ H) :
    ((ProjectionPerturbation.bbf P).graph K).Walk X Z := by
  classical
  by_cases hXZ : X = Z
  · subst Z
    exact SimpleGraph.Walk.nil
  · exact Classical.choose (P.exists_bbf_standard_walk_within_two hK hXZ)

/-- Every competing walk passes within two of every vertex of the chosen BBF
walk, including the equal-endpoint case. -/
theorem chosenBBFWalk_within_two
    (P : ProjectionSystem (G ⧸ H)) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    (X Z : G ⧸ H)
    (competing : ((ProjectionPerturbation.bbf P).graph K).Walk X Z)
    {Y : G ⧸ H} (hY : Y ∈ (chosenBBFWalk P hK X Z).support) :
    ∃ W, W ∈ competing.support ∧
      ((ProjectionPerturbation.bbf P).graph K).dist Y W ≤ 2 := by
  classical
  by_cases hXZ : X = Z
  · subst Z
    have hYX : Y = X := by
      simpa [chosenBBFWalk] using hY
    subst Y
    exact ⟨X, competing.start_mem_support, by simp⟩
  · have hchosen := P.exists_bbf_standard_walk_within_two hK hXZ
    have hproperty := Classical.choose_spec hchosen
    have hY' : Y ∈ (Classical.choose hchosen).support := by
      simpa [chosenBBFWalk, hXZ] using hY
    exact hproperty competing Y hY'

namespace Lift

/-- Vertices lifting a coset walk.  Index zero is the prescribed initial
representative; graph-walk vertices use fixed representatives thereafter; and
indices after the graph walk use the prescribed terminal representative. -/
noncomputable def vertex (H : Subgroup G) {Gamma : SimpleGraph (G ⧸ H)}
    {X Z : G ⧸ H} (p : Gamma.Walk X Z) (x z : G) (i : ℕ) : G :=
  if i = 0 then x
  else if i ≤ p.length then CosetGraph.representative H (p.getVert i)
  else z

@[simp] theorem vertex_zero (H : Subgroup G)
    {Gamma : SimpleGraph (G ⧸ H)} {X Z : G ⧸ H}
    (p : Gamma.Walk X Z) (x z : G) :
    vertex H p x z 0 = x := by
  simp [vertex]

@[simp] theorem vertex_length_add_one (H : Subgroup G)
    {Gamma : SimpleGraph (G ⧸ H)} {X Z : G ⧸ H}
    (p : Gamma.Walk X Z) (x z : G) :
    vertex H p x z (p.length + 1) = z := by
  simp [vertex]

/-- Up through the graph-walk length, a lifted vertex projects to `getVert`. -/
theorem mk_vertex_of_le (H : Subgroup G)
    {Gamma : SimpleGraph (G ⧸ H)} {X Z : G ⧸ H}
    (p : Gamma.Walk X Z) (x z : G) (hx : QuotientGroup.mk x = X)
    {i : ℕ} (hi : i ≤ p.length) :
    QuotientGroup.mk (vertex H p x z i) = p.getVert i := by
  by_cases hi0 : i = 0
  · subst i
    simp [hx, p.getVert_zero]
  · simp [vertex, hi0, hi, CosetGraph.mk_representative]

/-- Every lifted path vertex projects into the support of the coset walk. -/
theorem mk_vertex_mem_support (H : Subgroup G)
    {Gamma : SimpleGraph (G ⧸ H)} {X Z : G ⧸ H}
    (p : Gamma.Walk X Z) (x z : G)
    (hx : QuotientGroup.mk x = X) (hz : QuotientGroup.mk z = Z)
    {i : ℕ} (hi : i ≤ p.length + 1) :
    QuotientGroup.mk (vertex H p x z i) ∈ p.support := by
  by_cases hwalk : i ≤ p.length
  · rw [mk_vertex_of_le H p x z hx hwalk]
    exact p.getVert_mem_support i
  · have hilast : i = p.length + 1 := by omega
    subst i
    rw [vertex_length_add_one, hz]
    exact p.end_mem_support

/-- Every coset-walk support vertex is represented by a lifted path vertex. -/
theorem exists_vertex_of_mem_support (H : Subgroup G)
    {Gamma : SimpleGraph (G ⧸ H)} {X Z : G ⧸ H}
    (p : Gamma.Walk X Z) (x z : G) (hx : QuotientGroup.mk x = X)
    {W : G ⧸ H} (hW : W ∈ p.support) :
    ∃ i : ℕ, i ≤ p.length + 1 ∧
      QuotientGroup.mk (vertex H p x z i) = W := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hW
  obtain ⟨i, hiW, hi⟩ := hW
  refine ⟨i, by omega, ?_⟩
  rw [mk_vertex_of_le H p x z hx hi, hiW]

/-- Consecutive lifted vertices have relative word distance at most one. -/
theorem wordDist_vertex_succ_le_one
    (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) {X Z : G ⧸ H}
    (p : Gamma.Walk X Z) (x z : G)
    (hx : QuotientGroup.mk x = X) (hz : QuotientGroup.mk z = Z)
    {i : ℕ} (hi : i < p.length + 1) :
    wordDist (CosetGraph.relGenSet H Gamma hinv hconn).alphabet.carrier
      (vertex H p x z i) (vertex H p x z (i + 1)) ≤ 1 := by
  by_cases hinside : i < p.length
  · have hiLe : i ≤ p.length := hinside.le
    have hi1Le : i + 1 ≤ p.length := hinside
    have hadj := p.adj_getVert_succ hinside
    apply CosetGraph.wordDist_le_one_of_adj_mk H Gamma hinv hconn
    rw [mk_vertex_of_le H p x z hx hiLe,
      mk_vertex_of_le H p x z hx hi1Le]
    exact hadj
  · have hieq : i = p.length := by omega
    subst i
    apply CosetGraph.wordDist_le_one_of_mk_eq H Gamma hinv hconn
    have hcur : QuotientGroup.mk (vertex H p x z p.length) = Z := by
      rw [mk_vertex_of_le H p x z hx le_rfl, p.getVert_length]
    have hnext : QuotientGroup.mk (vertex H p x z (p.length + 1)) = Z := by
      rw [vertex_length_add_one, hz]
    exact hcur.trans hnext.symm

end Lift

/-- Length of the relative guessing path obtained from the chosen BBF walk. -/
noncomputable def bbfGuessLen
    (P : ProjectionSystem (G ⧸ H)) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    (x y : G) : ℕ :=
  (chosenBBFWalk P hK (QuotientGroup.mk x) (QuotientGroup.mk y)).length + 1

/-- The relative guessing path lifting the chosen BBF standard walk. -/
noncomputable def bbfGuessPath
    (P : ProjectionSystem (G ⧸ H)) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    (x y : G) (i : ℕ) : G :=
  Lift.vertex H
    (chosenBBFWalk P hK (QuotientGroup.mk x) (QuotientGroup.mk y)) x y i

@[simp] theorem bbfGuessPath_zero
    (P : ProjectionSystem (G ⧸ H)) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    (x y : G) :
    bbfGuessPath P hK x y 0 = x := by
  simp [bbfGuessPath]

@[simp] theorem bbfGuessPath_finish
    (P : ProjectionSystem (G ⧸ H)) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    (x y : G) :
    bbfGuessPath P hK x y (bbfGuessLen P hK x y) = y := by
  simp [bbfGuessPath, bbfGuessLen]

/-- The lifted BBF guessing path advances one relative letter at a time. -/
theorem bbfGuessPath_step
    (P : ProjectionSystem (G ⧸ H)) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      ((ProjectionPerturbation.bbf P).graph K).Adj (a • A) (a • B) ↔
        ((ProjectionPerturbation.bbf P).graph K).Adj A B)
    (x y : G) (i : ℕ) (hi : i < bbfGuessLen P hK x y) :
    wordDist (CosetGraph.relGenSet H
        ((ProjectionPerturbation.bbf P).graph K) hinv
        (P.bbf_graph_preconnected (by linarith [hK, P.ξ_pos]))).alphabet.carrier
      (bbfGuessPath P hK x y i) (bbfGuessPath P hK x y (i + 1)) ≤ 1 := by
  exact Lift.wordDist_vertex_succ_le_one H _ hinv _
    (chosenBBFWalk P hK (QuotientGroup.mk x) (QuotientGroup.mk y)) x y
    rfl rfl hi

/-- A lifted guessing vertex projects into its chosen standard-walk support. -/
theorem mk_bbfGuessPath_mem_support
    (P : ProjectionSystem (G ⧸ H)) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    (x y : G) {i : ℕ} (hi : i ≤ bbfGuessLen P hK x y) :
    QuotientGroup.mk (bbfGuessPath P hK x y i) ∈
      (chosenBBFWalk P hK (QuotientGroup.mk x) (QuotientGroup.mk y)).support := by
  exact Lift.mk_vertex_mem_support H _ x y rfl rfl hi

/-- Every chosen standard-walk support vertex has a representative on the
lifted guessing path. -/
theorem exists_bbfGuessPath_of_mem_support
    (P : ProjectionSystem (G ⧸ H)) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    (x y : G) {W : G ⧸ H}
    (hW : W ∈
      (chosenBBFWalk P hK (QuotientGroup.mk x) (QuotientGroup.mk y)).support) :
    ∃ i : ℕ, i ≤ bbfGuessLen P hK x y ∧
      QuotientGroup.mk (bbfGuessPath P hK x y i) = W := by
  exact Lift.exists_vertex_of_mem_support H _ x y rfl hW

/-- Guessing paths of relative-distance-one endpoints have diameter at most
six. -/
theorem bbfGuessPath_short
    (P : ProjectionSystem (G ⧸ H)) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      ((ProjectionPerturbation.bbf P).graph K).Adj (a • A) (a • B) ↔
        ((ProjectionPerturbation.bbf P).graph K).Adj A B)
    (x y : G)
    (hxy : wordDist (CosetGraph.relGenSet H
        ((ProjectionPerturbation.bbf P).graph K) hinv
        (P.bbf_graph_preconnected (by linarith [hK, P.ξ_pos]))).alphabet.carrier
      x y ≤ 1)
    {i j : ℕ} (hi : i ≤ bbfGuessLen P hK x y)
    (hj : j ≤ bbfGuessLen P hK x y) :
    wordDist (CosetGraph.relGenSet H
        ((ProjectionPerturbation.bbf P).graph K) hinv
        (P.bbf_graph_preconnected (by linarith [hK, P.ξ_pos]))).alphabet.carrier
      (bbfGuessPath P hK x y i) (bbfGuessPath P hK x y j) ≤ 6 := by
  let Gamma := (ProjectionPerturbation.bbf P).graph K
  have hpre : Gamma.Preconnected :=
    P.bbf_graph_preconnected (by linarith [hK, P.ξ_pos])
  have hproj : Gamma.dist (QuotientGroup.mk x) (QuotientGroup.mk y) ≤ 1 :=
    le_trans (CosetGraph.graph_dist_le_wordDist H Gamma hinv hpre x y) hxy
  obtain ⟨competing, hcompeting⟩ :=
    (CosetGraph.connected_of_preconnected H Gamma hpre).exists_walk_length_eq_dist
      (QuotientGroup.mk x) (QuotientGroup.mk y)
  have hcompLen : competing.length ≤ 1 := by omega
  have hiSupport := mk_bbfGuessPath_mem_support P hK x y hi
  have hjSupport := mk_bbfGuessPath_mem_support P hK x y hj
  obtain ⟨Wi, hWi, hiWi⟩ :=
    chosenBBFWalk_within_two P hK _ _ competing hiSupport
  obtain ⟨Wj, hWj, hjWj⟩ :=
    chosenBBFWalk_within_two P hK _ _ competing hjSupport
  have hWiWj := CosetGraph.dist_le_walk_length_of_mem_support
    (CosetGraph.connected_of_preconnected H Gamma hpre) competing hWi hWj
  have hWiWjOne : Gamma.dist Wi Wj ≤ 1 := le_trans hWiWj hcompLen
  have hiWi' : Gamma.dist
      (QuotientGroup.mk (bbfGuessPath P hK x y i)) Wi ≤ 2 := hiWi
  have hjWj' : Gamma.dist
      (QuotientGroup.mk (bbfGuessPath P hK x y j)) Wj ≤ 2 := hjWj
  have htriangle1 := (CosetGraph.connected_of_preconnected H Gamma hpre).dist_triangle
    (u := QuotientGroup.mk (bbfGuessPath P hK x y i)) (v := Wi) (w := Wj)
  have htriangle2 := (CosetGraph.connected_of_preconnected H Gamma hpre).dist_triangle
    (u := QuotientGroup.mk (bbfGuessPath P hK x y i)) (v := Wj)
    (w := QuotientGroup.mk (bbfGuessPath P hK x y j))
  have hWjj : Gamma.dist Wj (QuotientGroup.mk (bbfGuessPath P hK x y j)) ≤ 2 := by
    rw [SimpleGraph.dist_comm]
    exact hjWj'
  have hgraph : Gamma.dist
      (QuotientGroup.mk (bbfGuessPath P hK x y i))
      (QuotientGroup.mk (bbfGuessPath P hK x y j)) ≤ 5 := by
    calc
      Gamma.dist (QuotientGroup.mk (bbfGuessPath P hK x y i))
          (QuotientGroup.mk (bbfGuessPath P hK x y j)) ≤
          Gamma.dist (QuotientGroup.mk (bbfGuessPath P hK x y i)) Wj +
            Gamma.dist Wj (QuotientGroup.mk (bbfGuessPath P hK x y j)) :=
        htriangle2
      _ ≤ (Gamma.dist (QuotientGroup.mk (bbfGuessPath P hK x y i)) Wi +
          Gamma.dist Wi Wj) +
            Gamma.dist Wj (QuotientGroup.mk (bbfGuessPath P hK x y j)) :=
        Nat.add_le_add_right htriangle1 _
      _ ≤ (2 + 1) + 2 :=
        Nat.add_le_add (Nat.add_le_add hiWi' hWiWjOne) hWjj
      _ = 5 := rfl
  have hword := CosetGraph.wordDist_le_graph_dist_add_one H Gamma hinv hpre
    (bbfGuessPath P hK x y i) (bbfGuessPath P hK x y j)
  exact hword.trans (by omega)

/-- Chosen BBF guessing triangles are three-thin in the relative word metric. -/
theorem bbfGuessPath_thin
    (P : ProjectionSystem (G ⧸ H)) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      ((ProjectionPerturbation.bbf P).graph K).Adj (a • A) (a • B) ↔
        ((ProjectionPerturbation.bbf P).graph K).Adj A B)
    (x y z : G) {i : ℕ} (hi : i ≤ bbfGuessLen P hK x y) :
    ∃ j : ℕ,
      (j ≤ bbfGuessLen P hK x z ∧
        wordDist (CosetGraph.relGenSet H
          ((ProjectionPerturbation.bbf P).graph K) hinv
          (P.bbf_graph_preconnected (by linarith [hK, P.ξ_pos]))).alphabet.carrier
          (bbfGuessPath P hK x y i) (bbfGuessPath P hK x z j) ≤ 3) ∨
      (j ≤ bbfGuessLen P hK z y ∧
        wordDist (CosetGraph.relGenSet H
          ((ProjectionPerturbation.bbf P).graph K) hinv
          (P.bbf_graph_preconnected (by linarith [hK, P.ξ_pos]))).alphabet.carrier
          (bbfGuessPath P hK x y i) (bbfGuessPath P hK z y j) ≤ 3) := by
  let Gamma := (ProjectionPerturbation.bbf P).graph K
  have hpre : Gamma.Preconnected :=
    P.bbf_graph_preconnected (by linarith [hK, P.ξ_pos])
  let left := chosenBBFWalk P hK (QuotientGroup.mk x) (QuotientGroup.mk z)
  let right := chosenBBFWalk P hK (QuotientGroup.mk z) (QuotientGroup.mk y)
  have hiSupport := mk_bbfGuessPath_mem_support P hK x y hi
  obtain ⟨W, hW, hiW⟩ := chosenBBFWalk_within_two P hK _ _
    (left.append right) hiSupport
  rw [SimpleGraph.Walk.mem_support_append_iff] at hW
  rcases hW with hWleft | hWright
  · obtain ⟨j, hj, hjW⟩ := exists_bbfGuessPath_of_mem_support P hK x z hWleft
    refine ⟨j, Or.inl ⟨hj, ?_⟩⟩
    have hword := CosetGraph.wordDist_le_graph_dist_add_one H Gamma hinv hpre
      (bbfGuessPath P hK x y i) (bbfGuessPath P hK x z j)
    have hgraph : Gamma.dist (QuotientGroup.mk (bbfGuessPath P hK x y i))
        (QuotientGroup.mk (bbfGuessPath P hK x z j)) ≤ 2 := by
      rw [hjW]
      exact hiW
    exact hword.trans (by omega)
  · obtain ⟨j, hj, hjW⟩ := exists_bbfGuessPath_of_mem_support P hK z y hWright
    refine ⟨j, Or.inr ⟨hj, ?_⟩⟩
    have hword := CosetGraph.wordDist_le_graph_dist_add_one H Gamma hinv hpre
      (bbfGuessPath P hK x y i) (bbfGuessPath P hK z y j)
    have hgraph : Gamma.dist (QuotientGroup.mk (bbfGuessPath P hK x y i))
        (QuotientGroup.mk (bbfGuessPath P hK z y j)) ≤ 2 := by
      rw [hjW]
      exact hiW
    exact hword.trans (by omega)

/-- The relative Cayley graph attached to an equivariant BBF coset graph is
hyperbolic.  This theorem applies the proved Bowditch criterion
`OsinEnlargement.guessingGeodesics` with constant six. -/
theorem exists_fourPoint_of_bbf_coset_graph
    (P : ProjectionSystem (G ⧸ H)) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      ((ProjectionPerturbation.bbf P).graph K).Adj (a • A) (a • B) ↔
        ((ProjectionPerturbation.bbf P).graph K).Adj A B) :
    ∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic
      (CosetGraph.relGenSet H ((ProjectionPerturbation.bbf P).graph K) hinv
        (P.bbf_graph_preconnected (by linarith [hK, P.ξ_pos]))).alphabet.carrier
      delta := by
  let Gamma := (ProjectionPerturbation.bbf P).graph K
  have hpre : Gamma.Preconnected :=
    P.bbf_graph_preconnected (by linarith [hK, P.ξ_pos])
  let D := CosetGraph.relGenSet H Gamma hinv hpre
  apply OsinEnlargement.guessingGeodesics G D.alphabet.carrier
    D.alphabet.symmetricGenerating 6 (bbfGuessLen P hK) (bbfGuessPath P hK)
  · exact bbfGuessPath_zero P hK
  · exact bbfGuessPath_finish P hK
  · exact bbfGuessPath_step P hK hinv
  · intro x y hxy i hi j hj
    exact bbfGuessPath_short P hK hinv x y hxy hi hj
  · intro x y z i hi
    obtain ⟨j, hj⟩ := bbfGuessPath_thin P hK hinv x y z hi
    refine ⟨j, ?_⟩
    rcases hj with hj | hj
    · exact Or.inl ⟨hj.1, hj.2.trans (by omega)⟩
    · exact Or.inr ⟨hj.1, hj.2.trans (by omega)⟩

end ProjectionSystem
end GGT
end GroupApproximation
