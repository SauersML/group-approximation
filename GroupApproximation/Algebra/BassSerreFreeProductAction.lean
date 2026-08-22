import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import GroupApproximation.Algebra.BinaryCoprodNormalForm

/-!
# The Bass--Serre coset action of a binary free product

This file isolates the part of the Bass--Serre tree construction that is
already completely algebraic.  For `F = G ∗ Multiplicative ℤ`, its vertices
are the left cosets of the two free factors and its edges are the translates
of the pair of base cosets.  Left multiplication gives the canonical action.

The graph is proved to be a tree by transporting binary free-product words to
Mathlib's indexed reduced normal forms.  The other key output is
`baseEdge_pointwiseStabilizer_eq_bot`: the pointwise stabilizer of the base
edge is trivial.  This is the finite-stabilizer input in the subsequent
WPD/acylindricity argument, proved directly from the two free-product
retractions.  No hyperbolicity or acylindricity assertion is stored as an
input here.
-/

namespace GroupApproximation
namespace BassSerreFreeProduct

open Monoid

universe u

variable (G : Type u) [Group G]

/-- The free product used in the pivot. -/
abbrev Ambient := Monoid.Coprod G (Multiplicative ℤ)

/-- The canonical copy of the left factor. -/
def leftFactor : Subgroup (Ambient G) :=
  MonoidHom.range (Monoid.Coprod.inl : G →* Ambient G)

/-- The canonical copy of the infinite cyclic right factor. -/
def rightFactor : Subgroup (Ambient G) :=
  MonoidHom.range
    (Monoid.Coprod.inr : Multiplicative ℤ →* Ambient G)

/-- The two free factors meet only in the identity. -/
theorem leftFactor_inf_rightFactor :
    leftFactor G ⊓ rightFactor G = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rcases hx.1 with ⟨a, ha⟩
  rcases hx.2 with ⟨b, hb⟩
  have hab :
      (Monoid.Coprod.inl a : Ambient G) = Monoid.Coprod.inr b :=
    ha.trans hb.symm
  have haone : a = 1 := by
    have := congrArg (Monoid.Coprod.fst : Ambient G →* G) hab
    simpa using this
  rw [← ha, haone, map_one]

/-- Vertices of the Bass--Serre coset graph: one color for each factor. -/
abbrev Vertex :=
  (Ambient G ⧸ leftFactor G) ⊕ (Ambient G ⧸ rightFactor G)

/-- The bipartite color of a Bass--Serre vertex. -/
def color : Vertex G → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

/-- Left multiplication on the two colors of cosets. -/
instance vertexMulAction : MulAction (Ambient G) (Vertex G) where
  smul g
    | Sum.inl x => Sum.inl (g • x)
    | Sum.inr x => Sum.inr (g • x)
  one_smul := by
    intro x
    cases x <;> simp
  mul_smul := by
    intro g h x
    cases x <;> simp [mul_smul]

/-- The base vertex of left-factor color. -/
def baseLeft : Vertex G :=
  Sum.inl (1 : Ambient G ⧸ leftFactor G)

/-- The base vertex of right-factor color. -/
def baseRight : Vertex G :=
  Sum.inr (1 : Ambient G ⧸ rightFactor G)

/-- An oriented edge is a translate of the two base cosets. -/
def IsOrientedEdge (v w : Vertex G) : Prop :=
  ∃ g : Ambient G, v = g • baseLeft G ∧ w = g • baseRight G

/-- An oriented edge always goes from the left color to the right color. -/
theorem isOrientedEdge_colors {v w : Vertex G}
    (h : IsOrientedEdge G v w) :
    (∃ x, v = Sum.inl x) ∧ ∃ y, w = Sum.inr y := by
  obtain ⟨g, rfl, rfl⟩ := h
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- The two orientations cannot occur simultaneously. -/
theorem not_isOrientedEdge_reverse {v w : Vertex G}
    (h : IsOrientedEdge G v w) : ¬ IsOrientedEdge G w v := by
  intro hr
  obtain ⟨⟨x, hv⟩, -⟩ := isOrientedEdge_colors G h
  obtain ⟨-, ⟨y, hv'⟩⟩ := isOrientedEdge_colors G hr
  rw [hv] at hv'
  exact Sum.noConfusion hv'

/-- The (undirected) Bass--Serre coset graph. -/
def graph : SimpleGraph (Vertex G) where
  Adj v w := IsOrientedEdge G v w ∨ IsOrientedEdge G w v
  symm := by
    intro v w h
    exact h.elim Or.inr Or.inl
  loopless := by
    intro v h
    rcases h with ⟨g, hv, hw⟩ | ⟨g, hv, hw⟩
    · have : g • baseLeft G = g • baseRight G := hv.symm.trans hw
      simpa [baseLeft, baseRight] using this
    · have : g • baseRight G = g • baseLeft G := hv.symm.trans hw
      simpa [baseLeft, baseRight] using this

/-- Adjacent vertices have opposite colors. -/
theorem color_ne_of_adj {v w : Vertex G} (h : (graph G).Adj v w) :
    color G v ≠ color G w := by
  change IsOrientedEdge G v w ∨ IsOrientedEdge G w v at h
  rcases h with h | h
  · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := isOrientedEdge_colors G h
    decide
  · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := isOrientedEdge_colors G h
    decide

/-- The action carries oriented edges to oriented edges. -/
theorem isOrientedEdge_smul (a : Ambient G) {v w : Vertex G}
    (h : IsOrientedEdge G v w) :
    IsOrientedEdge G (a • v) (a • w) := by
  obtain ⟨g, rfl, rfl⟩ := h
  exact ⟨a * g, by simp [mul_smul], by simp [mul_smul]⟩

/-- Left multiplication preserves adjacency in both directions. -/
theorem adj_smul_iff (a : Ambient G) (v w : Vertex G) :
    (graph G).Adj (a • v) (a • w) ↔ (graph G).Adj v w := by
  change
    (IsOrientedEdge G (a • v) (a • w) ∨
      IsOrientedEdge G (a • w) (a • v)) ↔
    (IsOrientedEdge G v w ∨ IsOrientedEdge G w v)
  constructor
  · intro h
    rcases h with hvw | hwv
    · left
      simpa only [inv_smul_smul] using isOrientedEdge_smul G a⁻¹ hvw
    · right
      simpa only [inv_smul_smul] using isOrientedEdge_smul G a⁻¹ hwv
  · intro h
    exact h.elim (fun hvw ↦ Or.inl (isOrientedEdge_smul G a hvw))
      (fun hwv ↦ Or.inr (isOrientedEdge_smul G a hwv))

/-- Left multiplication as a graph homomorphism. -/
def actionHom (a : Ambient G) : graph G →g graph G where
  toFun v := a • v
  map_rel' := fun {_ _} h ↦ (adj_smul_iff G a _ _).mpr h

/-- Reachability is preserved by left multiplication. -/
theorem Reachable.smul (a : Ambient G) {v w : Vertex G}
    (h : (graph G).Reachable v w) :
    (graph G).Reachable (a • v) (a • w) :=
  h.map (actionHom G a)

/-- The two base vertices form an edge. -/
theorem base_adj : (graph G).Adj (baseLeft G) (baseRight G) :=
  Or.inl ⟨1, by simp [baseLeft], by simp [baseRight]⟩

/-- Fixing the left base coset is exactly membership in the left factor. -/
theorem smul_baseLeft_eq_iff (g : Ambient G) :
    g • baseLeft G = baseLeft G ↔ g ∈ leftFactor G := by
  change
    (g • (1 : Ambient G ⧸ leftFactor G)) = 1 ↔
      g ∈ leftFactor G
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
  simp

/-- Fixing the right base coset is exactly membership in the right factor. -/
theorem smul_baseRight_eq_iff (g : Ambient G) :
    g • baseRight G = baseRight G ↔ g ∈ rightFactor G := by
  change
    (g • (1 : Ambient G ⧸ rightFactor G)) = 1 ↔
      g ∈ rightFactor G
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
  simp

/-- Every translate of either base vertex is reachable from the left base
vertex.  This uses only the coproduct induction principle: a left-factor
letter fixes `baseLeft`, while a right-factor letter fixes `baseRight` and
crosses the base edge. -/
theorem reachable_translates (g : Ambient G) :
    (graph G).Reachable (baseLeft G) (g • baseLeft G) ∧
      (graph G).Reachable (baseLeft G) (g • baseRight G) := by
  induction g using Monoid.Coprod.induction_on' with
  | one =>
      exact ⟨by simp, (base_adj G).reachable⟩
  | inl_mul a x ih =>
      have hfix :
          (Monoid.Coprod.inl a : Ambient G) • baseLeft G = baseLeft G :=
        (smul_baseLeft_eq_iff G _).mpr ⟨a, rfl⟩
      constructor
      · simpa only [mul_smul, hfix] using
          ih.1.smul G (Monoid.Coprod.inl a : Ambient G)
      · simpa only [mul_smul, hfix] using
          ih.2.smul G (Monoid.Coprod.inl a : Ambient G)
  | inr_mul b x ih =>
      have hfix :
          (Monoid.Coprod.inr b : Ambient G) • baseRight G = baseRight G :=
        (smul_baseRight_eq_iff G _).mpr ⟨b, rfl⟩
      have hcross : (graph G).Reachable (baseLeft G)
          ((Monoid.Coprod.inr b : Ambient G) • baseLeft G) :=
        (base_adj G).reachable.trans <| by
          have := (base_adj G).reachable.smul G
            (Monoid.Coprod.inr b : Ambient G)
          simpa only [hfix] using this.symm
      constructor
      · exact hcross.trans <| by
          simpa only [mul_smul] using
            ih.1.smul G (Monoid.Coprod.inr b : Ambient G)
      · exact hcross.trans <| by
          simpa only [mul_smul] using
            ih.2.smul G (Monoid.Coprod.inr b : Ambient G)

/-- Every vertex is reachable from the left base vertex. -/
theorem reachable_from_baseLeft (v : Vertex G) :
    (graph G).Reachable (baseLeft G) v := by
  rcases v with v | v
  · refine QuotientGroup.induction_on v ?_
    intro g
    exact (reachable_translates G g).1
  · refine QuotientGroup.induction_on v ?_
    intro g
    exact (reachable_translates G g).2

/-- The Bass--Serre coset graph is connected. -/
theorem graph_connected : (graph G).Connected := by
  refine ⟨?_, ⟨baseLeft G⟩⟩
  intro v w
  exact (reachable_from_baseLeft G v).symm.trans (reachable_from_baseLeft G w)

/-- The ordered endpoints of the base edge. -/
def baseEdge : Vertex G × Vertex G := (baseLeft G, baseRight G)

/-- An element fixing both endpoints of the base edge is the identity. -/
theorem smul_baseEdge_eq_iff (g : Ambient G) :
    g • baseEdge G = baseEdge G ↔ g = 1 := by
  constructor
  · intro h
    have hleft : g • baseLeft G = baseLeft G := congrArg Prod.fst h
    have hright : g • baseRight G = baseRight G := congrArg Prod.snd h
    have hg : g ∈ leftFactor G ⊓ rightFactor G :=
      ⟨(smul_baseLeft_eq_iff G g).mp hleft,
        (smul_baseRight_eq_iff G g).mp hright⟩
    rw [leftFactor_inf_rightFactor G] at hg
    simpa using hg
  · rintro rfl
    exact one_smul _ _

/-- The group element labeling an oriented edge is unique. -/
theorem orientedEdge_label_unique {v w : Vertex G} {g h : Ambient G}
    (hg : v = g • baseLeft G ∧ w = g • baseRight G)
    (hh : v = h • baseLeft G ∧ w = h • baseRight G) : g = h := by
  have hedge : g • baseEdge G = h • baseEdge G := by
    apply Prod.ext
    · exact hg.1.symm.trans hh.1
    · exact hg.2.symm.trans hh.2
  have hfix : (h⁻¹ * g) • baseEdge G = baseEdge G := by
    calc
      (h⁻¹ * g) • baseEdge G = h⁻¹ • (g • baseEdge G) := by
        simp [mul_smul]
      _ = h⁻¹ • (h • baseEdge G) := by rw [hedge]
      _ = baseEdge G := inv_smul_smul h _
  have hone : h⁻¹ * g = 1 := (smul_baseEdge_eq_iff G _).mp hfix
  exact inv_mul_eq_one.mp hone

/-- Each oriented edge has a unique label. -/
theorem existsUnique_orientedEdge_label {v w : Vertex G}
    (h : IsOrientedEdge G v w) :
    ∃! g : Ambient G,
      v = g • baseLeft G ∧ w = g • baseRight G := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, hg, fun y hy ↦ orientedEdge_label_unique G hy hg⟩

/-- The canonical label of an undirected edge.  Its orientation is recovered
from the colors of its endpoints. -/
noncomputable def edgeLabel {v w : Vertex G} (h : (graph G).Adj v w) :
    Ambient G := by
  classical
  change IsOrientedEdge G v w ∨ IsOrientedEdge G w v at h
  exact if ho : IsOrientedEdge G v w then
    Classical.choose ho
  else
    Classical.choose (h.resolve_left ho)

/-- The edge label realizes one of the two possible endpoint orientations. -/
theorem edgeLabel_spec {v w : Vertex G} (h : (graph G).Adj v w) :
    (v = edgeLabel G h • baseLeft G ∧
        w = edgeLabel G h • baseRight G) ∨
      (w = edgeLabel G h • baseLeft G ∧
        v = edgeLabel G h • baseRight G) := by
  classical
  change IsOrientedEdge G v w ∨ IsOrientedEdge G w v at h
  rw [edgeLabel]
  split_ifs with ho
  · exact Or.inl (Classical.choose_spec ho)
  · exact Or.inr (Classical.choose_spec (h.resolve_left ho))

/-- Equal edge labels determine the same undirected edge. -/
theorem edge_eq_of_edgeLabel_eq {u v x y : Vertex G}
    (h₁ : (graph G).Adj u v) (h₂ : (graph G).Adj x y)
    (heq : edgeLabel G h₁ = edgeLabel G h₂) :
    s(u, v) = s(x, y) := by
  rcases edgeLabel_spec G h₁ with h₁f | h₁r <;>
    rcases edgeLabel_spec G h₂ with h₂f | h₂r <;>
    simp_all

/-- Edge labels along a walk, in traversal order. -/
noncomputable def walkLabels : {v w : Vertex G} →
    (graph G).Walk v w → List (Ambient G)
  | _, _, .nil => []
  | _, _, .cons h p => edgeLabel G h :: walkLabels G p

@[simp] theorem walkLabels_nil (v : Vertex G) :
    walkLabels G ((graph G).Walk.nil : (graph G).Walk v v) = [] := rfl

@[simp] theorem walkLabels_cons {u v w : Vertex G}
    (h : (graph G).Adj u v) (p : (graph G).Walk v w) :
    walkLabels G (.cons h p) = edgeLabel G h :: walkLabels G p := rfl

/-- There is exactly one label per traversed edge. -/
theorem length_walkLabels {v w : Vertex G} (p : (graph G).Walk v w) :
    (walkLabels G p).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [ih]

/-- Labels respect concatenation of walks. -/
theorem walkLabels_append {u v w : Vertex G}
    (p : (graph G).Walk u v) (q : (graph G).Walk v w) :
    walkLabels G (p.append q) = walkLabels G p ++ walkLabels G q := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [ih]

/-- Membership in the label list comes from a concrete traversed edge with
that label. -/
theorem exists_edge_of_mem_walkLabels {v w : Vertex G}
    (p : (graph G).Walk v w) {a : Ambient G}
    (ha : a ∈ walkLabels G p) :
    ∃ (x y : Vertex G) (h : (graph G).Adj x y),
      s(x, y) ∈ p.edges ∧ edgeLabel G h = a := by
  induction p with
  | nil => simp at ha
  | @cons x y z h p ih =>
      rw [walkLabels_cons, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact ⟨x, y, h, by simp, rfl⟩
      · obtain ⟨x', y', h', hedge, hlabel⟩ := ih ha
        exact ⟨x', y', h', by simp [hedge], hlabel⟩

/-- A trail has no repeated edge labels. -/
theorem walkLabels_nodup_of_isTrail {v w : Vertex G}
    {p : (graph G).Walk v w} (hp : p.IsTrail) :
    (walkLabels G p).Nodup := by
  induction p with
  | nil => exact List.nodup_nil
  | @cons x y z h p ih =>
      rw [SimpleGraph.Walk.isTrail_def, SimpleGraph.Walk.edges_cons,
        List.nodup_cons] at hp
      rw [walkLabels_cons, List.nodup_cons]
      refine ⟨?_, ih hp.2⟩
      intro hmem
      obtain ⟨x', y', h', hedge, hlabel⟩ :=
        exists_edge_of_mem_walkLabels G p hmem
      apply hp.1
      rw [edge_eq_of_edgeLabel_eq G h h' hlabel]
      exact hedge

/-- Closing a nontrivial duplicate-free list back at its first entry preserves
consecutive inequality (although, of course, not global `Nodup`). -/
theorem isChain_ne_append_head_of_nodup {A : Type*} {a : A} {l : List A}
    (hn : (a :: l).Nodup) (hl : l ≠ []) :
    (a :: (l ++ [a])).IsChain (· ≠ ·) := by
  rw [← List.cons_append, List.isChain_append]
  refine ⟨hn.isChain, List.IsChain.singleton _, ?_⟩
  intro x hx y hy
  simp only [List.head?_singleton, Option.mem_some_iff] at hy
  subst y
  have hx' : x ∈ l.getLast? := by
    cases l with
    | nil => exact (hl rfl).elim
    | cons b t => simpa only [List.getLast?_cons_cons] using hx
  intro hxa
  apply hn.1
  rw [← hxa]
  exact List.mem_of_mem_getLast? hx'

/-- Successive quotients starting from `g`. -/
def transitionsFrom (g : Ambient G) : List (Ambient G) → List (Ambient G)
  | [] => []
  | h :: t => (g⁻¹ * h) :: transitionsFrom G h t

/-- A nonempty cyclic label list yields the successive quotients around the
cycle, including the closing quotient back to the first label. -/
def cyclicTransitions : List (Ambient G) → List (Ambient G)
  | [] => []
  | g :: t => transitionsFrom G g (t ++ [g])

/-- The product of successive quotients telescopes. -/
theorem prod_transitionsFrom (g : Ambient G) :
    ∀ l : List (Ambient G),
      g * (transitionsFrom G g l).prod = l.getLastD g := by
  intro l
  induction l generalizing g with
  | nil => simp [transitionsFrom]
  | cons h t ih =>
      simp only [transitionsFrom, List.prod_cons, mul_assoc,
        mul_inv_cancel_left, List.getLastD_cons]
      exact ih h

/-- **The transition word of every nonempty cyclic label list multiplies to
the identity.** -/
theorem prod_cyclicTransitions {g : Ambient G} (t : List (Ambient G)) :
    (cyclicTransitions G (g :: t)).prod = 1 := by
  have htel := prod_transitionsFrom G g (t ++ [g])
  have hlast : (t ++ [g]).getLastD g = g := by simp
  rw [hlast] at htel
  rw [cyclicTransitions]
  exact mul_left_cancel (a := g) (by simpa using htel)

/-- Equality at a left-colored endpoint says that the quotient of the two
incident edge labels lies in the left factor. -/
theorem inv_mul_mem_leftFactor_of_smul_baseLeft_eq {g h : Ambient G}
    (heq : g • baseLeft G = h • baseLeft G) :
    g⁻¹ * h ∈ leftFactor G := by
  have heq' : (g : Ambient G ⧸ leftFactor G) = h := by
    simpa [baseLeft, smul_eq_mul] using heq
  exact QuotientGroup.eq.mp heq'

/-- The analogous transition statement at a right-colored endpoint. -/
theorem inv_mul_mem_rightFactor_of_smul_baseRight_eq {g h : Ambient G}
    (heq : g • baseRight G = h • baseRight G) :
    g⁻¹ * h ∈ rightFactor G := by
  have heq' : (g : Ambient G ⧸ rightFactor G) = h := by
    simpa [baseRight, smul_eq_mul] using heq
  exact QuotientGroup.eq.mp heq'

/-- Distinct incident edge labels give a nonidentity transition syllable. -/
theorem inv_mul_ne_one_of_ne {g h : Ambient G} (hne : g ≠ h) :
    g⁻¹ * h ≠ 1 := by
  simpa [inv_mul_eq_one] using hne

/-- At two consecutive edges, the quotient of their labels lies in the factor
whose color is the shared vertex. -/
theorem adjacentLabels_transition_mem {u v w : Vertex G}
    (h₁ : (graph G).Adj u v) (h₂ : (graph G).Adj v w) :
    match v with
    | Sum.inl _ => edgeLabel G h₁⁻¹ * edgeLabel G h₂ ∈ leftFactor G
    | Sum.inr _ => edgeLabel G h₁⁻¹ * edgeLabel G h₂ ∈ rightFactor G := by
  rcases s₁ : edgeLabel_spec G h₁ with h₁f | h₁r
  · rcases s₂ : edgeLabel_spec G h₂ with h₂f | h₂r
    · rcases v with v | v
      · exact Sum.noConfusion h₁f.2
      · exact Sum.noConfusion h₂f.1
    · rcases v with v | v
      · exact Sum.noConfusion h₁f.2
      · apply inv_mul_mem_rightFactor_of_smul_baseRight_eq G
        exact h₁f.2.symm.trans h₂r.2
  · rcases s₂ : edgeLabel_spec G h₂ with h₂f | h₂r
    · rcases v with v | v
      · apply inv_mul_mem_leftFactor_of_smul_baseLeft_eq G
        exact h₁r.1.symm.trans h₂f.1
      · exact Sum.noConfusion h₁r.1
    · rcases v with v | v
      · exact Sum.noConfusion h₂r.1
      · exact Sum.noConfusion h₁r.1

/-- A transition known to lie in the factor selected by a shared vertex,
encoded as a dependent letter of the indexed free product. -/
noncomputable def transitionLetter (v : Vertex G) (t : Ambient G)
    (ht : match v with
      | Sum.inl _ => t ∈ leftFactor G
      | Sum.inr _ => t ∈ rightFactor G) :
    Σ i, BinaryCoprodNormalForm.factor G i := by
  classical
  cases v with
  | inl _ =>
      obtain ⟨g, hg⟩ := ht
      exact ⟨false, g⟩
  | inr _ =>
      obtain ⟨z, hz⟩ := ht
      exact ⟨true, MulEquiv.ulift.symm z⟩

@[simp] theorem transitionLetter_fst (v : Vertex G) (t : Ambient G)
    (ht : match v with
      | Sum.inl _ => t ∈ leftFactor G
      | Sum.inr _ => t ∈ rightFactor G) :
    (transitionLetter G v t ht).1 = color G v := by
  cases v <;> rfl

/-- Decoding a transition letter recovers the original binary-free-product
element. -/
theorem fromIndexed_of_transitionLetter (v : Vertex G) (t : Ambient G)
    (ht : match v with
      | Sum.inl _ => t ∈ leftFactor G
      | Sum.inr _ => t ∈ rightFactor G) :
    BinaryCoprodNormalForm.fromIndexed G
        (CoprodI.of (transitionLetter G v t ht).2) = t := by
  classical
  cases v with
  | inl _ =>
      obtain ⟨g, hg⟩ := ht
      simp only [transitionLetter,
        BinaryCoprodNormalForm.fromIndexed_of_false]
      exact hg
  | inr _ =>
      obtain ⟨z, hz⟩ := ht
      simp only [transitionLetter,
        BinaryCoprodNormalForm.fromIndexed_of_true]
      simpa using hz

/-- A nonidentity transition decodes to a nonidentity dependent letter. -/
theorem transitionLetter_ne_one (v : Vertex G) (t : Ambient G)
    (ht : match v with
      | Sum.inl _ => t ∈ leftFactor G
      | Sum.inr _ => t ∈ rightFactor G)
    (htone : t ≠ 1) : (transitionLetter G v t ht).2 ≠ 1 := by
  intro hone
  apply htone
  rw [← fromIndexed_of_transitionLetter G v t ht, hone, map_one]

/-- Dependent transition letters between one preceding edge and each edge of
a following walk.  For a closed walk this contains every transition except
the final closing transition. -/
noncomputable def linearTransitionLetters : {u v w : Vertex G} →
    (h : (graph G).Adj u v) → (graph G).Walk v w →
      List (Σ i, BinaryCoprodNormalForm.factor G i)
  | _, _, _, _, .nil => []
  | _, v, _, h₁, .cons h₂ p =>
      let ht := adjacentLabels_transition_mem G h₁ h₂
      transitionLetter G v (edgeLabel G h₁⁻¹ * edgeLabel G h₂) ht ::
        linearTransitionLetters G h₂ p

@[simp] theorem linearTransitionLetters_nil {u v : Vertex G}
    (h : (graph G).Adj u v) :
    linearTransitionLetters G h ((graph G).Walk.nil : (graph G).Walk v v) = [] := rfl

@[simp] theorem linearTransitionLetters_cons {u v w z : Vertex G}
    (h₁ : (graph G).Adj u v) (h₂ : (graph G).Adj v w)
    (p : (graph G).Walk w z) :
    linearTransitionLetters G h₁ (.cons h₂ p) =
      transitionLetter G v (edgeLabel G h₁⁻¹ * edgeLabel G h₂)
          (adjacentLabels_transition_mem G h₁ h₂) ::
        linearTransitionLetters G h₂ p := rfl

theorem length_linearTransitionLetters {u v w : Vertex G}
    (h : (graph G).Adj u v) (p : (graph G).Walk v w) :
    (linearTransitionLetters G h p).length = p.length := by
  induction p with
  | nil => rfl
  | cons h₂ p ih => simp [ih]

/-- Indices of consecutive linear transition letters alternate, because they
are the colors of consecutive shared vertices. -/
theorem linearTransitionLetters_chain_ne {u v w : Vertex G}
    (h : (graph G).Adj u v) (p : (graph G).Walk v w) :
    (linearTransitionLetters G h p).IsChain fun a b ↦ a.1 ≠ b.1 := by
  induction p generalizing u with
  | nil => exact List.isChain_nil
  | @cons x y z h₂ p ih =>
      cases p with
      | nil => exact List.IsChain.singleton _
      | @cons y z q h₃ p =>
          rw [linearTransitionLetters_cons, linearTransitionLetters_cons,
            List.isChain_cons_cons]
          refine ⟨?_, ?_⟩
          · simpa only [transitionLetter_fst] using color_ne_of_adj G h₂
          · exact ih h₂

/-- Consecutively distinct edge labels make every linear transition letter
nonidentity. -/
theorem linearTransitionLetters_ne_one_of_chain {u v w : Vertex G}
    (h : (graph G).Adj u v) (p : (graph G).Walk v w)
    (hn : (edgeLabel G h :: walkLabels G p).IsChain (· ≠ ·)) :
    ∀ q ∈ linearTransitionLetters G h p, q.2 ≠ 1 := by
  induction p generalizing u with
  | nil => simp
  | @cons x y z h₂ p ih =>
      rw [walkLabels_cons, List.isChain_cons_cons] at hn
      rw [linearTransitionLetters_cons, List.forall_mem_cons]
      refine ⟨?_, ih h₂ hn.2⟩
      apply transitionLetter_ne_one G
      exact inv_mul_ne_one_of_ne G hn.1

/-- A duplicate-free label list is in particular consecutively distinct. -/
theorem linearTransitionLetters_ne_one {u v w : Vertex G}
    (h : (graph G).Adj u v) (p : (graph G).Walk v w)
    (hn : (edgeLabel G h :: walkLabels G p).Nodup) :
    ∀ q ∈ linearTransitionLetters G h p, q.2 ≠ 1 :=
  linearTransitionLetters_ne_one_of_chain G h p hn.isChain

/-- The reduced indexed word carried by a consecutively-distinct edge-label
sequence. -/
noncomputable def linearTransitionWord {u v w : Vertex G}
    (h : (graph G).Adj u v) (p : (graph G).Walk v w)
    (hn : (edgeLabel G h :: walkLabels G p).IsChain (· ≠ ·)) :
    CoprodI.Word (BinaryCoprodNormalForm.factor G) where
  toList := linearTransitionLetters G h p
  ne_one := linearTransitionLetters_ne_one_of_chain G h p hn
  chain_ne := linearTransitionLetters_chain_ne G h p

@[simp] theorem linearTransitionWord_toList {u v w : Vertex G}
    (h : (graph G).Adj u v) (p : (graph G).Walk v w)
    (hn : (edgeLabel G h :: walkLabels G p).IsChain (· ≠ ·)) :
    (linearTransitionWord G h p hn).toList =
      linearTransitionLetters G h p := rfl

/-- Decoding the indexed transition word gives the product of the binary
transition list. -/
theorem fromIndexed_prod_linearTransitionWord {u v w : Vertex G}
    (h : (graph G).Adj u v) (p : (graph G).Walk v w)
    (hn : (edgeLabel G h :: walkLabels G p).IsChain (· ≠ ·)) :
    BinaryCoprodNormalForm.fromIndexed G (linearTransitionWord G h p hn).prod =
      (transitionsFrom G (edgeLabel G h) (walkLabels G p)).prod := by
  induction p generalizing u with
  | nil => simp [linearTransitionWord, CoprodI.Word.prod, transitionsFrom]
  | @cons x y z h₂ p ih =>
      rw [walkLabels_cons, List.isChain_cons_cons] at hn
      rw [linearTransitionWord, CoprodI.Word.prod, linearTransitionLetters_cons,
        List.map_cons, List.prod_cons, map_mul,
        fromIndexed_of_transitionLetter, transitionsFrom, List.prod_cons]
      congr 1
      simpa [linearTransitionWord, CoprodI.Word.prod] using ih h₂ hn.2

/-- The Bass--Serre coset graph has no cycles.  A hypothetical cycle supplies
a nonempty reduced transition word: trailness makes consecutive edge labels
distinct, bipartiteness makes the transition factors alternate, and the
transition product telescopes to `1`, contradicting binary free-product normal
form. -/
theorem graph_isAcyclic : (graph G).IsAcyclic := by
  intro start c hc
  cases c with
  | nil => exact hc.not_nil rfl
  | @cons start next _ h p =>
      let q : (graph G).Walk next next := p.append h.toWalk
      have hn : (edgeLabel G h :: walkLabels G p).Nodup := by
        simpa using walkLabels_nodup_of_isTrail G hc.isTrail
      have hpLabels : walkLabels G p ≠ [] := by
        intro hempty
        have hlen := length_walkLabels G p
        rw [hempty] at hlen
        have hthree := hc.three_le_length
        rw [SimpleGraph.Walk.length_cons] at hthree
        simp at hlen
        omega
      have hclosedChain :
          (edgeLabel G h :: (walkLabels G p ++ [edgeLabel G h])).IsChain
            (· ≠ ·) :=
        isChain_ne_append_head_of_nodup hn hpLabels
      have hqLabels :
          walkLabels G q = walkLabels G p ++ [edgeLabel G h] := by
        dsimp [q]
        rw [walkLabels_append]
        simp
      have hchain :
          (edgeLabel G h :: walkLabels G q).IsChain (· ≠ ·) := by
        rw [hqLabels]
        exact hclosedChain
      let W := linearTransitionWord G h q hchain
      have hWnonempty : W.toList ≠ [] := by
        intro hnil
        have hlen := length_linearTransitionLetters G h q
        change (linearTransitionLetters G h q).length = q.length at hlen
        have hzero : (linearTransitionLetters G h q).length = 0 := by
          simpa [W, linearTransitionWord] using congrArg List.length hnil
        have hqpos : 0 < q.length := by
          dsimp [q]
          simp
        omega
      have hdecode := fromIndexed_prod_linearTransitionWord G h q hchain
      have htransitionOne :
          (transitionsFrom G (edgeLabel G h) (walkLabels G q)).prod = 1 := by
        rw [hqLabels]
        exact prod_cyclicTransitions G (walkLabels G p)
      have hWone : BinaryCoprodNormalForm.fromIndexed G W.prod = 1 := by
        exact hdecode.trans htransitionOne
      exact
        (BinaryCoprodNormalForm.fromIndexed_prod_ne_one_of_toList_ne_nil G hWnonempty)
          hWone

/-- **The canonical Bass--Serre coset graph of `G ∗ ℤ` is a tree.** -/
theorem graph_isTree : (graph G).IsTree :=
  ⟨graph_connected G, graph_isAcyclic G⟩

/-- **The base edge has trivial pointwise stabilizer.**  In particular it is
finite, which is the algebraic core of the WPD segment argument for the
Bass--Serre action. -/
theorem baseEdge_pointwiseStabilizer_eq_bot :
    MulAction.stabilizer (Ambient G) (baseEdge G) = ⊥ := by
  ext g
  rw [MulAction.mem_stabilizer_iff, smul_baseEdge_eq_iff G]
  exact (Subgroup.mem_bot).symm

/-- The base-edge pointwise stabilizer is finite (indeed, trivial). -/
theorem finite_baseEdge_pointwiseStabilizer :
    Finite (MulAction.stabilizer (Ambient G) (baseEdge G)) := by
  rw [baseEdge_pointwiseStabilizer_eq_bot G]
  infer_instance

/-- Every translate of the base edge has trivial pointwise stabilizer. -/
theorem smul_translatedBaseEdge_eq_iff (g x : Ambient G) :
    x • (g • baseEdge G) = g • baseEdge G ↔ x = 1 := by
  constructor
  · intro h
    have hc : (g⁻¹ * x * g) • baseEdge G = baseEdge G := by
      calc
        (g⁻¹ * x * g) • baseEdge G =
            g⁻¹ • (x • (g • baseEdge G)) := by simp [mul_smul]
        _ = g⁻¹ • (g • baseEdge G) := by rw [h]
        _ = baseEdge G := inv_smul_smul g _
    have hconj : g⁻¹ * x * g = 1 :=
      (smul_baseEdge_eq_iff G (g⁻¹ * x * g)).mp hc
    calc
      x = g * (g⁻¹ * x * g) * g⁻¹ := by simp [mul_assoc]
      _ = 1 := by rw [hconj]; simp
  · rintro rfl
    exact one_smul _ _

/-- Every translated oriented edge has trivial pointwise stabilizer. -/
theorem translatedBaseEdge_pointwiseStabilizer_eq_bot (g : Ambient G) :
    MulAction.stabilizer (Ambient G) (g • baseEdge G) = ⊥ := by
  ext x
  rw [MulAction.mem_stabilizer_iff, smul_translatedBaseEdge_eq_iff G]
  exact (Subgroup.mem_bot).symm

/-- **Every edge of the Bass--Serre coset graph has trivial pointwise
stabilizer.**  This is the zero-error edge-stabilizer input to the usual
acylindricity argument; by itself it does not assert the bounded-displacement
quantifiers in the definition of an acylindrical action.  It also does not
depend on the still-separate proof that the graph is a tree. -/
theorem adjacentPair_pointwiseStabilizer_eq_bot {v w : Vertex G}
    (hvw : (graph G).Adj v w) :
    MulAction.stabilizer (Ambient G) (v, w) = ⊥ := by
  change IsOrientedEdge G v w ∨ IsOrientedEdge G w v at hvw
  rcases hvw with ⟨g, rfl, rfl⟩ | ⟨g, rfl, rfl⟩
  · change MulAction.stabilizer (Ambient G) (g • baseEdge G) = ⊥
    exact translatedBaseEdge_pointwiseStabilizer_eq_bot G g
  · ext x
    rw [MulAction.mem_stabilizer_iff]
    change
      (x • (g • baseRight G), x • (g • baseLeft G)) =
          (g • baseRight G, g • baseLeft G) ↔ x ∈ (⊥ : Subgroup (Ambient G))
    rw [Prod.mk.injEq, and_comm]
    change x • (g • baseEdge G) = g • baseEdge G ↔ _
    rw [smul_translatedBaseEdge_eq_iff G]
    exact (Subgroup.mem_bot).symm

/-- In particular, the pointwise stabilizer of every graph edge is finite. -/
theorem finite_adjacentPair_pointwiseStabilizer {v w : Vertex G}
    (hvw : (graph G).Adj v w) :
    Finite (MulAction.stabilizer (Ambient G) (v, w)) := by
  rw [adjacentPair_pointwiseStabilizer_eq_bot G hvw]
  infer_instance

end BassSerreFreeProduct
end GroupApproximation
