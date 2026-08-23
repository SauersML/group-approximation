import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import GroupApproximation.Algebra.BinaryCoprodNormalForm
import GroupApproximation.Algebra.FreeProductConjugacy

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

noncomputable local instance factorDecidableEq
    (i : Bool) : DecidableEq (BinaryCoprodNormalForm.factor G i) :=
  Classical.decEq _

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
    cases x with
    | inl x => exact congrArg Sum.inl (one_smul (Ambient G) x)
    | inr x => exact congrArg Sum.inr (one_smul (Ambient G) x)
  mul_smul := by
    intro g h x
    cases x with
    | inl x => exact congrArg Sum.inl (mul_smul g h x)
    | inr x => exact congrArg Sum.inr (mul_smul g h x)

/-- The base vertex of left-factor color. -/
def baseLeft : Vertex G :=
  Sum.inl (QuotientGroup.mk (s := leftFactor G) 1)

/-- The base vertex of right-factor color. -/
def baseRight : Vertex G :=
  Sum.inr (QuotientGroup.mk (s := rightFactor G) 1)

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
  exact Sum.inl_ne_inr (hv.symm.trans hv')

/-- The (undirected) Bass--Serre coset graph. -/
def graph : SimpleGraph (Vertex G) where
  Adj v w := IsOrientedEdge G v w ∨ IsOrientedEdge G w v
  symm := ⟨by
    intro v w h
    exact h.elim Or.inr Or.inl⟩
  loopless := ⟨by
    intro v h
    rcases h with ⟨g, hv, hw⟩ | ⟨g, hv, hw⟩
    · obtain ⟨⟨x, hleft⟩, ⟨y, hright⟩⟩ :=
        isOrientedEdge_colors G ⟨g, hv, hw⟩
      exact Sum.inl_ne_inr (hleft.symm.trans hright)
    · obtain ⟨⟨x, hleft⟩, ⟨y, hright⟩⟩ :=
        isOrientedEdge_colors G ⟨g, hv, hw⟩
      exact Sum.inl_ne_inr (hleft.symm.trans hright)⟩

/-- Adjacent vertices have opposite colors. -/
theorem color_ne_of_adj {v w : Vertex G} (h : (graph G).Adj v w) :
    color G v ≠ color G w := by
  change IsOrientedEdge G v w ∨ IsOrientedEdge G w v at h
  rcases h with h | h
  · obtain ⟨⟨x, hv⟩, ⟨y, hw⟩⟩ := isOrientedEdge_colors G h
    intro hc
    have : false = true := by
      calc
        false = color G v := by rw [hv]; rfl
        _ = color G w := hc
        _ = true := by rw [hw]; rfl
    exact Bool.false_ne_true this
  · obtain ⟨⟨x, hw⟩, ⟨y, hv⟩⟩ := isOrientedEdge_colors G h
    intro hc
    have : true = false := by
      calc
        true = color G v := by rw [hv]; rfl
        _ = color G w := hc
        _ = false := by rw [hw]; rfl
    exact Bool.false_ne_true this.symm

/-- Left translation preserves the bipartite color. -/
@[simp] theorem color_smul (a : Ambient G) (v : Vertex G) :
    color G (a • v) = color G v := by
  cases v <;> rfl

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
  h.elim fun p ↦ ⟨p.map (actionHom G a)⟩

/-- The two base vertices form an edge. -/
theorem base_adj : (graph G).Adj (baseLeft G) (baseRight G) :=
  Or.inl ⟨1, by simp [baseLeft], by simp [baseRight]⟩

/-- Fixing the left base coset is exactly membership in the left factor. -/
theorem smul_baseLeft_eq_iff (g : Ambient G) :
    g • baseLeft G = baseLeft G ↔ g ∈ leftFactor G := by
  change
    Sum.inl (g • QuotientGroup.mk (s := leftFactor G) 1) =
        Sum.inl (QuotientGroup.mk (s := leftFactor G) 1) ↔
      g ∈ leftFactor G
  rw [Sum.inl.injEq, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
    QuotientGroup.eq]
  simp

/-- Fixing the right base coset is exactly membership in the right factor. -/
theorem smul_baseRight_eq_iff (g : Ambient G) :
    g • baseRight G = baseRight G ↔ g ∈ rightFactor G := by
  change
    Sum.inr (g • QuotientGroup.mk (s := rightFactor G) 1) =
        Sum.inr (QuotientGroup.mk (s := rightFactor G) 1) ↔
      g ∈ rightFactor G
  rw [Sum.inr.injEq, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
    QuotientGroup.eq]
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
          Reachable.smul G (Monoid.Coprod.inl a : Ambient G) ih.1
      · simpa only [mul_smul, hfix] using
          Reachable.smul G (Monoid.Coprod.inl a : Ambient G) ih.2
  | inr_mul b x ih =>
      have hfix :
          (Monoid.Coprod.inr b : Ambient G) • baseRight G = baseRight G :=
        (smul_baseRight_eq_iff G _).mpr ⟨b, rfl⟩
      have hcross : (graph G).Reachable (baseLeft G)
          ((Monoid.Coprod.inr b : Ambient G) • baseLeft G) :=
        (base_adj G).reachable.trans <| by
          have := Reachable.smul G (Monoid.Coprod.inr b : Ambient G)
            (base_adj G).reachable
          simpa only [hfix] using this.symm
      constructor
      · exact hcross.trans <| by
          simpa only [mul_smul] using
            Reachable.smul G (Monoid.Coprod.inr b : Ambient G) ih.1
      · exact hcross.trans <| by
          simpa only [mul_smul] using
            Reachable.smul G (Monoid.Coprod.inr b : Ambient G) ih.2

/-- Every vertex is reachable from the left base vertex. -/
theorem reachable_from_baseLeft (v : Vertex G) :
    (graph G).Reachable (baseLeft G) v := by
  rcases v with v | v
  · refine QuotientGroup.induction_on v ?_
    intro g
    have heq : g • baseLeft G =
        Sum.inl (QuotientGroup.mk (s := leftFactor G) g) := by
      change Sum.inl (g • QuotientGroup.mk (s := leftFactor G) 1) = _
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    rw [← heq]
    exact (reachable_translates G g).1
  · refine QuotientGroup.induction_on v ?_
    intro g
    have heq : g • baseRight G =
        Sum.inr (QuotientGroup.mk (s := rightFactor G) g) := by
      change Sum.inr (g • QuotientGroup.mk (s := rightFactor G) 1) = _
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    rw [← heq]
    exact (reachable_translates G g).2

/-- The Bass--Serre coset graph is connected. -/
theorem graph_connected : (graph G).Connected := by
  refine { preconnected := ?_, nonempty := ⟨baseLeft G⟩ }
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
  exact (inv_mul_eq_one.mp hone).symm

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
    rcases edgeLabel_spec G h₂ with h₂f | h₂r
  · calc
      s(u, v) = s(edgeLabel G h₁ • baseLeft G,
          edgeLabel G h₁ • baseRight G) := congrArg₂ (fun a b ↦ s(a, b)) h₁f.1 h₁f.2
      _ = s(edgeLabel G h₂ • baseLeft G,
          edgeLabel G h₂ • baseRight G) := by rw [heq]
      _ = s(x, y) := (congrArg₂ (fun a b ↦ s(a, b)) h₂f.1 h₂f.2).symm
  · calc
      s(u, v) = s(edgeLabel G h₁ • baseLeft G,
          edgeLabel G h₁ • baseRight G) := congrArg₂ (fun a b ↦ s(a, b)) h₁f.1 h₁f.2
      _ = s(edgeLabel G h₂ • baseLeft G,
          edgeLabel G h₂ • baseRight G) := by rw [heq]
      _ = s(edgeLabel G h₂ • baseRight G,
          edgeLabel G h₂ • baseLeft G) := Sym2.eq_swap
      _ = s(x, y) := (congrArg₂ (fun a b ↦ s(a, b)) h₂r.2 h₂r.1).symm
  · calc
      s(u, v) = s(edgeLabel G h₁ • baseRight G,
          edgeLabel G h₁ • baseLeft G) := congrArg₂ (fun a b ↦ s(a, b)) h₁r.2 h₁r.1
      _ = s(edgeLabel G h₁ • baseLeft G,
          edgeLabel G h₁ • baseRight G) := Sym2.eq_swap
      _ = s(edgeLabel G h₂ • baseLeft G,
          edgeLabel G h₂ • baseRight G) := by rw [heq]
      _ = s(x, y) := (congrArg₂ (fun a b ↦ s(a, b)) h₂f.1 h₂f.2).symm
  · calc
      s(u, v) = s(edgeLabel G h₁ • baseRight G,
          edgeLabel G h₁ • baseLeft G) := congrArg₂ (fun a b ↦ s(a, b)) h₁r.2 h₁r.1
      _ = s(edgeLabel G h₂ • baseRight G,
          edgeLabel G h₂ • baseLeft G) := by rw [heq]
      _ = s(x, y) := (congrArg₂ (fun a b ↦ s(a, b)) h₂r.2 h₂r.1).symm

/-- Edge labels along a walk, in traversal order. -/
noncomputable def walkLabels {v w : Vertex G}
    (p : (graph G).Walk v w) : List (Ambient G) :=
  p.darts.map fun d ↦ edgeLabel G d.adj

@[simp] theorem walkLabels_nil (v : Vertex G) :
    walkLabels G (.nil : (graph G).Walk v v) = [] := rfl

@[simp] theorem walkLabels_cons {u v w : Vertex G}
    (h : (graph G).Adj u v) (p : (graph G).Walk v w) :
    walkLabels G (.cons h p) = edgeLabel G h :: walkLabels G p := by
  simp [walkLabels]

/-- There is exactly one label per traversed edge. -/
theorem length_walkLabels {v w : Vertex G} (p : (graph G).Walk v w) :
    (walkLabels G p).length = p.length := by
  simp [walkLabels]

/-- Labels respect concatenation of walks. -/
theorem walkLabels_append {u v w : Vertex G}
    (p : (graph G).Walk u v) (q : (graph G).Walk v w) :
    walkLabels G (p.append q) = walkLabels G p ++ walkLabels G q := by
  simp [walkLabels, SimpleGraph.Walk.darts_append]

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
      have hpn := hp.edges_nodup
      rw [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hpn
      rw [walkLabels_cons, List.nodup_cons]
      refine ⟨?_, ih ⟨hpn.2⟩⟩
      intro hmem
      obtain ⟨x', y', h', hedge, hlabel⟩ :=
        exists_edge_of_mem_walkLabels G p hmem
      apply hpn.1
      rw [edge_eq_of_edgeLabel_eq G h h' hlabel.symm]
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
  rw [List.nodup_cons] at hn
  apply hn.1
  rw [← hxa]
  exact List.mem_of_mem_getLast? hx'

/-- Successive quotients starting from `g`. -/
def transitionsFrom (g : Ambient G) : List (Ambient G) → List (Ambient G)
  | [] => []
  | h :: t => (g⁻¹ * h) :: transitionsFrom h t

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
  change Sum.inl (g • QuotientGroup.mk (s := leftFactor G) 1) =
    Sum.inl (h • QuotientGroup.mk (s := leftFactor G) 1) at heq
  have hmk :
      QuotientGroup.mk (s := leftFactor G) g =
        QuotientGroup.mk (s := leftFactor G) h := by
    simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] using
      (Sum.inl.inj heq)
  exact QuotientGroup.eq.mp hmk

/-- The analogous transition statement at a right-colored endpoint. -/
theorem inv_mul_mem_rightFactor_of_smul_baseRight_eq {g h : Ambient G}
    (heq : g • baseRight G = h • baseRight G) :
    g⁻¹ * h ∈ rightFactor G := by
  change Sum.inr (g • QuotientGroup.mk (s := rightFactor G) 1) =
    Sum.inr (h • QuotientGroup.mk (s := rightFactor G) 1) at heq
  have hmk :
      QuotientGroup.mk (s := rightFactor G) g =
        QuotientGroup.mk (s := rightFactor G) h := by
    simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] using
      (Sum.inr.inj heq)
  exact QuotientGroup.eq.mp hmk

/-- Distinct incident edge labels give a nonidentity transition syllable. -/
theorem inv_mul_ne_one_of_ne {g h : Ambient G} (hne : g ≠ h) :
    g⁻¹ * h ≠ 1 := by
  simpa [inv_mul_eq_one] using hne

/-- At two consecutive edges, the quotient of their labels lies in the factor
whose color is the shared vertex. -/
theorem adjacentLabels_transition_mem {u v w : Vertex G}
    (h₁ : (graph G).Adj u v) (h₂ : (graph G).Adj v w) :
    match v with
    | Sum.inl _ => (edgeLabel G h₁)⁻¹ * edgeLabel G h₂ ∈ leftFactor G
    | Sum.inr _ => (edgeLabel G h₁)⁻¹ * edgeLabel G h₂ ∈ rightFactor G := by
  cases v with
  | inl v =>
      rcases edgeLabel_spec G h₁ with h₁f | h₁r
      · exact (Sum.inl_ne_inr h₁f.2).elim
      · rcases edgeLabel_spec G h₂ with h₂f | h₂r
        · apply inv_mul_mem_leftFactor_of_smul_baseLeft_eq G
          exact h₁r.1.symm.trans h₂f.1
        · exact (Sum.inl_ne_inr h₂r.2).elim
  | inr v =>
      rcases edgeLabel_spec G h₁ with h₁f | h₁r
      · rcases edgeLabel_spec G h₂ with h₂f | h₂r
        · exact (Sum.inl_ne_inr h₂f.1.symm).elim
        · apply inv_mul_mem_rightFactor_of_smul_baseRight_eq G
          exact h₁f.2.symm.trans h₂r.2
      · exact (Sum.inl_ne_inr h₁r.1.symm).elim

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
      exact ⟨false, Classical.choose ht⟩
  | inr _ =>
      exact ⟨true, ULift.up (Classical.choose ht)⟩

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
      change Monoid.Coprod.inl (Classical.choose ht) = t
      exact Classical.choose_spec ht
  | inr _ =>
      change Monoid.Coprod.inr (Classical.choose ht) = t
      exact Classical.choose_spec ht

/-- A nonidentity transition decodes to a nonidentity dependent letter. -/
theorem transitionLetter_ne_one (v : Vertex G) (t : Ambient G)
    (ht : match v with
      | Sum.inl _ => t ∈ leftFactor G
      | Sum.inr _ => t ∈ rightFactor G)
    (htone : t ≠ 1) : (transitionLetter G v t ht).2 ≠ 1 := by
  intro hone
  apply htone
  have hdecode := fromIndexed_of_transitionLetter G v t ht
  rw [hone] at hdecode
  simpa using hdecode.symm

/-- The canonical dependent letter attached to two consecutive edges.  The
shared vertex is eliminated here once, so recursive walk constructions do not
carry proof-sensitive `match` terms in their equations. -/
noncomputable def adjacentTransitionLetter {u v w : Vertex G}
    (h₁ : (graph G).Adj u v) (h₂ : (graph G).Adj v w) :
    Σ i, BinaryCoprodNormalForm.factor G i := by
  cases v with
  | inl v =>
      have ht :
          (edgeLabel G h₁)⁻¹ * edgeLabel G h₂ ∈ leftFactor G :=
        adjacentLabels_transition_mem G h₁ h₂
      exact transitionLetter G (Sum.inl v)
        ((edgeLabel G h₁)⁻¹ * edgeLabel G h₂) ht
  | inr v =>
      have ht :
          (edgeLabel G h₁)⁻¹ * edgeLabel G h₂ ∈ rightFactor G :=
        adjacentLabels_transition_mem G h₁ h₂
      exact transitionLetter G (Sum.inr v)
        ((edgeLabel G h₁)⁻¹ * edgeLabel G h₂) ht

@[simp] theorem adjacentTransitionLetter_fst {u v w : Vertex G}
    (h₁ : (graph G).Adj u v) (h₂ : (graph G).Adj v w) :
    (adjacentTransitionLetter G h₁ h₂).1 = color G v := by
  cases v <;> simp [adjacentTransitionLetter, transitionLetter_fst]

/-- Decoding the canonical adjacent-edge letter gives the quotient of the two
edge labels. -/
theorem fromIndexed_of_adjacentTransitionLetter {u v w : Vertex G}
    (h₁ : (graph G).Adj u v) (h₂ : (graph G).Adj v w) :
    BinaryCoprodNormalForm.fromIndexed G
        (CoprodI.of (adjacentTransitionLetter G h₁ h₂).2) =
      (edgeLabel G h₁)⁻¹ * edgeLabel G h₂ := by
  cases v with
  | inl v =>
      unfold adjacentTransitionLetter
      apply fromIndexed_of_transitionLetter
  | inr v =>
      unfold adjacentTransitionLetter
      apply fromIndexed_of_transitionLetter

/-- Distinct adjacent edge labels make the canonical dependent letter
nonidentity. -/
theorem adjacentTransitionLetter_ne_one {u v w : Vertex G}
    (h₁ : (graph G).Adj u v) (h₂ : (graph G).Adj v w)
    (hne : edgeLabel G h₁ ≠ edgeLabel G h₂) :
    (adjacentTransitionLetter G h₁ h₂).2 ≠ 1 := by
  intro hone
  apply inv_mul_ne_one_of_ne G hne
  have hdecode := fromIndexed_of_adjacentTransitionLetter G h₁ h₂
  rw [hone] at hdecode
  simpa using hdecode.symm

/-- Dependent transition letters between one preceding edge and each edge of
a following walk.  For a closed walk this contains every transition except
the final closing transition. -/
noncomputable def linearTransitionLetters {u v w : Vertex G}
    (h₁ : (graph G).Adj u v) : (graph G).Walk v w →
      List (Σ i, BinaryCoprodNormalForm.factor G i)
  | .nil => []
  | .cons h₂ p =>
      adjacentTransitionLetter G h₁ h₂ :: linearTransitionLetters h₂ p

@[simp] theorem linearTransitionLetters_nil {u v : Vertex G}
    (h : (graph G).Adj u v) :
    linearTransitionLetters G h (.nil : (graph G).Walk v v) = [] := rfl

@[simp] theorem linearTransitionLetters_cons {u v w z : Vertex G}
    (h₁ : (graph G).Adj u v) (h₂ : (graph G).Adj v w)
    (p : (graph G).Walk w z) :
    linearTransitionLetters G h₁ (.cons h₂ p) =
      adjacentTransitionLetter G h₁ h₂ :: linearTransitionLetters G h₂ p := rfl

theorem length_linearTransitionLetters {u v w : Vertex G}
    (h : (graph G).Adj u v) (p : (graph G).Walk v w) :
    (linearTransitionLetters G h p).length = p.length := by
  induction p generalizing u with
  | nil => rfl
  | cons h₂ p ih =>
      rw [linearTransitionLetters_cons, List.length_cons,
        SimpleGraph.Walk.length_cons]
      exact congrArg Nat.succ (ih h₂)

/-- Indices of consecutive linear transition letters alternate, because they
are the colors of consecutive shared vertices. -/
theorem linearTransitionLetters_chain_ne {u v w : Vertex G}
    (h : (graph G).Adj u v) (p : (graph G).Walk v w) :
    (linearTransitionLetters G h p).IsChain fun a b ↦ a.1 ≠ b.1 := by
  induction p generalizing u with
  | nil => exact List.isChain_nil
  | @cons x y z h₂ p ih =>
      cases p with
      | nil =>
          rw [linearTransitionLetters_cons, linearTransitionLetters_nil]
          exact List.IsChain.singleton _
      | @cons y z q h₃ p =>
          rw [linearTransitionLetters_cons, linearTransitionLetters_cons,
            List.isChain_cons_cons]
          refine ⟨?_, ?_⟩
          · simpa only [adjacentTransitionLetter_fst] using color_ne_of_adj G h₂
          · exact ih h₂

/-- Consecutively distinct edge labels make every linear transition letter
nonidentity. -/
theorem linearTransitionLetters_ne_one_of_chain {u v w : Vertex G}
    (h : (graph G).Adj u v) (p : (graph G).Walk v w)
    (hn : (edgeLabel G h :: walkLabels G p).IsChain (· ≠ ·)) :
    ∀ q ∈ linearTransitionLetters G h p, q.2 ≠ 1 := by
  induction p generalizing u with
  | nil => simp [linearTransitionLetters]
  | @cons x y z h₂ p ih =>
      rw [walkLabels_cons, List.isChain_cons_cons] at hn
      intro q hq
      rw [linearTransitionLetters_cons, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact adjacentTransitionLetter_ne_one G h h₂ hn.1
      · exact ih h₂ hn.2 q hq

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
  change
    BinaryCoprodNormalForm.fromIndexed G
        ((linearTransitionLetters G h p).map
          (fun q ↦ CoprodI.of q.2)).prod =
      (transitionsFrom G (edgeLabel G h) (walkLabels G p)).prod
  induction p generalizing u with
  | nil => rfl
  | @cons x y z h₂ p ih =>
      have hnTail :
          (edgeLabel G h₂ :: walkLabels G p).IsChain (· ≠ ·) := by
        simp only [walkLabels_cons] at hn
        exact hn.tail
      rw [linearTransitionLetters_cons, List.map_cons, List.prod_cons, map_mul,
        fromIndexed_of_adjacentTransitionLetter, walkLabels_cons, transitionsFrom,
        List.prod_cons, ih h₂ hnTail]

/-- The Bass--Serre coset graph has no cycles.  A hypothetical cycle supplies
a nonempty reduced transition word: trailness makes consecutive edge labels
distinct, bipartiteness makes the transition factors alternate, and the
transition product telescopes to `1`, contradicting binary free-product normal
form. -/
theorem graph_isAcyclic : (graph G).IsAcyclic := by
  intro start c hc
  cases c with
  | nil => exact hc.not_nil (by simp)
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

/-! ## Normal-form length controls Bass--Serre displacement -/

/-- At a left-colored endpoint, the canonical label of an incident edge
sends the left base vertex to that endpoint. -/
theorem edgeLabel_smul_baseLeft_eq_of_color_eq_false {v w : Vertex G}
    (h : (graph G).Adj v w) (hv : color G v = false) :
    edgeLabel G h • baseLeft G = v := by
  rcases edgeLabel_spec G h with hf | hr
  · exact hf.1.symm
  · exfalso
    have : color G v = true := by rw [hr.2]; rfl
    exact Bool.false_ne_true (hv.symm.trans this)

/-- The last label of a nonempty walk sends the left base vertex to the end
whenever that end has left color.  Stating this with `getLastD` avoids a
separate nonemptiness witness for the tail of the walk. -/
theorem getLastD_walkLabels_smul_baseLeft_eq_end {u v w target : Vertex G}
    (h : (graph G).Adj u v) (p : (graph G).Walk v w)
    (hend : p.getVert p.length = target) (hw : color G target = false) :
    (walkLabels G p).getLastD (edgeLabel G h) • baseLeft G =
      target := by
  induction p generalizing u target with
  | nil =>
      have hv : _ = target := by
        simpa [SimpleGraph.Walk.getVert] using hend
      exact (edgeLabel_smul_baseLeft_eq_of_color_eq_false G h (by
        rw [hv]
        exact hw)).trans hv
  | @cons x y z h' p ih =>
      simp only [walkLabels_cons, List.getLastD_cons]
      apply ih h' target
      · simpa using hend
      · exact hw

/-- A binary-free-product element lying in the left factor has indexed
syllable length at most one. -/
theorem sylLength_toIndexed_le_one_of_mem_leftFactor {a : Ambient G}
    (ha : a ∈ leftFactor G) :
    FreeProductCyclic.sylLength (BinaryCoprodNormalForm.toIndexed G a) ≤ 1 := by
  classical
  rcases ha with ⟨x, rfl⟩
  rw [BinaryCoprodNormalForm.toIndexed_inl]
  exact FreeProductCyclic.sylLength_of_le_one
    (G := BinaryCoprodNormalForm.factor G) (i := false) x

/-- The transition product of a consecutively-distinct edge-label sequence
has exactly one indexed syllable per transition. -/
theorem sylLength_toIndexed_prod_transitionsFrom {u v w : Vertex G}
    (h : (graph G).Adj u v) (p : (graph G).Walk v w)
    (hn : (edgeLabel G h :: walkLabels G p).IsChain (· ≠ ·)) :
    FreeProductCyclic.sylLength
        (BinaryCoprodNormalForm.toIndexed G
          (transitionsFrom G (edgeLabel G h) (walkLabels G p)).prod) =
      p.length := by
  classical
  let W := linearTransitionWord G h p hn
  have hdecode := fromIndexed_prod_linearTransitionWord G h p hn
  have hprod : W.prod = BinaryCoprodNormalForm.toIndexed G
      (transitionsFrom G (edgeLabel G h) (walkLabels G p)).prod := by
    calc
      W.prod = BinaryCoprodNormalForm.toIndexed G
          (BinaryCoprodNormalForm.fromIndexed G W.prod) := by
            have hc := DFunLike.congr_fun
              (BinaryCoprodNormalForm.toIndexed_comp_fromIndexed G) W.prod
            exact hc.symm
      _ = BinaryCoprodNormalForm.toIndexed G
          (transitionsFrom G (edgeLabel G h) (walkLabels G p)).prod :=
            congrArg (BinaryCoprodNormalForm.toIndexed G) hdecode
  change (CoprodI.Word.equiv
    (BinaryCoprodNormalForm.toIndexed G
      (transitionsFrom G (edgeLabel G h) (walkLabels G p)).prod)).toList.length =
        p.length
  rw [← hprod]
  have hW : CoprodI.Word.equiv W.prod = W :=
    CoprodI.Word.equiv.apply_symm_apply W
  rw [hW]
  exact length_linearTransitionLetters G h p

/-- Every simple walk from the left base vertex to its translate gives an
upper bound on the indexed reduced-word length.  The two extra factor letters
are the stabilizer corrections at the endpoints; there is one transition
letter for every edge after the first. -/
theorem sylLength_toIndexed_le_path_length_add_one {g : Ambient G}
    {x y : Vertex G} (p : (graph G).Walk x y)
    (hx : x = baseLeft G) (hy : y = g • baseLeft G) (hp : p.IsPath)
    (hpos : 0 < p.length) :
    FreeProductCyclic.sylLength (BinaryCoprodNormalForm.toIndexed G g) ≤
      p.length + 1 := by
  classical
  cases p with
  | nil =>
      simp at hpos
  | @cons _ v _ h q =>
      have hn : (edgeLabel G h :: walkLabels G q).Nodup :=
        walkLabels_nodup_of_isTrail G hp.isTrail
      have hfirst : edgeLabel G h • baseLeft G = baseLeft G :=
        (edgeLabel_smul_baseLeft_eq_of_color_eq_false G h (by
          rw [hx]
          rfl)).trans hx
      have hfirstMem : edgeLabel G h ∈ leftFactor G :=
        (smul_baseLeft_eq_iff G (edgeLabel G h)).mp hfirst
      let last := (walkLabels G q).getLastD (edgeLabel G h)
      have hlast : last • baseLeft G = g • baseLeft G := by
        apply getLastD_walkLabels_smul_baseLeft_eq_end G h q
          (target := g • baseLeft G)
        · simpa using hy
        · simp
      have hlastMem : last⁻¹ * g ∈ leftFactor G :=
        inv_mul_mem_leftFactor_of_smul_baseLeft_eq G hlast
      let t := (transitionsFrom G (edgeLabel G h) (walkLabels G q)).prod
      have htel : edgeLabel G h * t = last := by
        exact prod_transitionsFrom G (edgeLabel G h) (walkLabels G q)
      have hg : g = edgeLabel G h * t * (last⁻¹ * g) := by
        rw [htel]
        simp
      have ht : FreeProductCyclic.sylLength
          (BinaryCoprodNormalForm.toIndexed G t) = q.length := by
        apply sylLength_toIndexed_prod_transitionsFrom G h q hn.isChain
      rw [hg, map_mul, map_mul]
      calc
        FreeProductCyclic.sylLength
            (BinaryCoprodNormalForm.toIndexed G (edgeLabel G h) *
              BinaryCoprodNormalForm.toIndexed G t *
                BinaryCoprodNormalForm.toIndexed G (last⁻¹ * g)) ≤
            FreeProductCyclic.sylLength
                (BinaryCoprodNormalForm.toIndexed G (edgeLabel G h) *
                  BinaryCoprodNormalForm.toIndexed G t) +
              FreeProductCyclic.sylLength
                (BinaryCoprodNormalForm.toIndexed G (last⁻¹ * g)) :=
          FreeProductCyclic.sylLength_mul_le _ _
        _ ≤ (FreeProductCyclic.sylLength
                (BinaryCoprodNormalForm.toIndexed G (edgeLabel G h)) +
              FreeProductCyclic.sylLength
                (BinaryCoprodNormalForm.toIndexed G t)) + 1 := by
          gcongr
          · exact FreeProductCyclic.sylLength_mul_le _ _
          · exact sylLength_toIndexed_le_one_of_mem_leftFactor G hlastMem
        _ ≤ (1 + q.length) + 1 := by
          rw [ht]
          gcongr
          exact sylLength_toIndexed_le_one_of_mem_leftFactor G hfirstMem
        _ = (SimpleGraph.Walk.cons h q).length + 1 := by
          simp [SimpleGraph.Walk.length_cons, Nat.add_comm]

/-- **Bass--Serre displacement lower bound.**  The graph displacement of the
left base vertex is at least the indexed reduced syllable length minus one. -/
theorem sylLength_toIndexed_sub_one_le_graph_dist (g : Ambient G) :
    FreeProductCyclic.sylLength (BinaryCoprodNormalForm.toIndexed G g) - 1 ≤
      (graph G).dist (baseLeft G) (g • baseLeft G) := by
  by_cases hfix : g • baseLeft G = baseLeft G
  · have hgmem := (smul_baseLeft_eq_iff G g).mp hfix
    have hlen := sylLength_toIndexed_le_one_of_mem_leftFactor G hgmem
    omega
  · obtain ⟨p, hp, hplen⟩ :=
      (graph_connected G).exists_path_of_dist (baseLeft G) (g • baseLeft G)
    have hdistPos : 0 < (graph G).dist (baseLeft G) (g • baseLeft G) := by
      have hne : baseLeft G ≠ g • baseLeft G := fun h ↦ hfix h.symm
      exact Nat.pos_of_ne_zero (fun hzero ↦ hne
        ((graph_connected G).dist_eq_zero_iff.mp hzero))
    have hpPos : 0 < p.length := by omega
    have hbound := sylLength_toIndexed_le_path_length_add_one G p rfl rfl hp hpPos
    omega

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
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hswap := (MulAction.mem_stabilizer_iff.mp hx)
    change
      (x • (g • baseRight G), x • (g • baseLeft G)) =
        (g • baseRight G, g • baseLeft G) at hswap
    have hbase : x • (g • baseEdge G) = g • baseEdge G := by
      change
        (x • (g • baseLeft G), x • (g • baseRight G)) =
          (g • baseLeft G, g • baseRight G)
      exact Prod.ext (congrArg Prod.snd hswap) (congrArg Prod.fst hswap)
    exact (smul_translatedBaseEdge_eq_iff G g x).mp hbase

/-- In particular, the pointwise stabilizer of every graph edge is finite. -/
theorem finite_adjacentPair_pointwiseStabilizer {v w : Vertex G}
    (hvw : (graph G).Adj v w) :
    Finite (MulAction.stabilizer (Ambient G) (v, w)) := by
  rw [adjacentPair_pointwiseStabilizer_eq_bot G hvw]
  infer_instance

end BassSerreFreeProduct
end GroupApproximation
