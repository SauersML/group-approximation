import GroupApproximation.GGT.VanKampen.Estimating.SelectionDichotomy

/-!
# Osin's incidence graph as a combinatorial map

`InteriorIncidencePlanarRealization` asks for Osin's `Phi_M` -- cells as
vertices, selected interior contiguity regions as edges -- realized as a
planar `CombMap` with the right vertex and edge counts.  This module builds
the half of that realization which is forced, and isolates the half which is
genuine geometry.

**Forced.**  A `CombMap` is a dart type with an edge reversal `alpha` and a
vertex rotation `sigma`.  For `Phi_M` the darts are the *incidences*: one per
endpoint of each interior edge.  That is exactly `E × Bool` for `E` the chosen
edge set, matching est's own `Embedded.interiorIncidenceEquiv`, which already
identifies interior incidences with `InteriorEdge selected × Bool`.  Edge
reversal is then the `Bool` flip, and the two `CombMap` laws are immediate.
`phiEdgeEquiv` computes the resulting edge set: `alpha`-orbits are exactly the
edges, so `edgeCount` is `Nat.card E` on the nose.

**Not forced, and not attempted here.**  The vertex rotation `sigma` is the
cyclic order of incidences around each cell, read off the cell's boundary
walk; the realization then needs its `sigma`-orbits to be the cells, and needs
planarity and face degree at least three transported from the disc.  Those are
named as `PhiVertexRotation` below rather than guessed at, since the cyclic
order is the geometric content of the construction.
-/

set_option linter.unusedVariables false

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

universe u w v

/-! ## The dart type and edge reversal -/

/-- Edge reversal on incidence darts: flip which endpoint of the edge the
incidence names. -/
def phiAlpha (E : Type v) : Equiv.Perm (E × Bool) where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv := by
    rintro ⟨e, b⟩
    simp
  right_inv := by
    rintro ⟨e, b⟩
    simp

@[simp] theorem phiAlpha_apply (E : Type v) (d : E × Bool) :
    phiAlpha E d = (d.1, !d.2) := rfl

theorem phiAlpha_involutive (E : Type v) :
    Function.Involutive (phiAlpha E) := by
  rintro ⟨e, b⟩
  simp

theorem phiAlpha_fixedPointFree (E : Type v) (d : E × Bool) :
    phiAlpha E d ≠ d := by
  rintro h
  have := congrArg Prod.snd h
  simp only [phiAlpha_apply] at this
  exact (Bool.not_ne_self d.2) this

/-- **Osin's `Phi_M` as a combinatorial map**, given the cyclic order of
incidences at each cell.  Only the vertex rotation is an input; the darts and
the edge reversal are determined. -/
def phiMap (E : Type v) [Fintype E] (sigma : Equiv.Perm (E × Bool)) :
    CombMap.{v} where
  Dart := E × Bool
  dartFintype := inferInstance
  alpha := phiAlpha E
  sigma := sigma
  alpha_involutive := phiAlpha_involutive E
  alpha_fixedPointFree := phiAlpha_fixedPointFree E

@[simp] theorem phiMap_dart (E : Type v) [Fintype E]
    (sigma : Equiv.Perm (E × Bool)) :
    (phiMap E sigma).Dart = (E × Bool) := rfl

/-! ## The edges of `Phi_M` are the interior edges -/

/-- The `alpha`-orbits of `Phi_M` are its edges: reversal only flips the
`Bool`, so each orbit is one interior edge. -/
noncomputable def phiEdgeEquiv (E : Type v) [Fintype E]
    (sigma : Equiv.Perm (E × Bool)) :
    (phiMap E sigma).Edge ≃ E where
  toFun := Quotient.lift (fun d : E × Bool => d.1) (by
    rintro ⟨e₁, b₁⟩ ⟨e₂, b₂⟩ (h | h)
    · exact congrArg Prod.fst h
    · have h' : ((e₁, !b₁) : E × Bool) = (e₂, b₂) := h
      have hfst : e₁ = e₂ := congrArg Prod.fst h'
      exact hfst)
  invFun e := Quotient.mk'' (e, false)
  left_inv := by
    refine Quotient.ind ?_
    rintro ⟨e, b⟩
    apply Quotient.sound
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  right_inv := by
    intro e
    rfl

/-- Consequently the edge count of `Phi_M` is the number of interior edges. -/
theorem phiMap_edgeCount (E : Type v) [Fintype E]
    (sigma : Equiv.Perm (E × Bool)) :
    (phiMap E sigma).edgeCount = Nat.card E :=
  Nat.card_eq_of_bijective _ (phiEdgeEquiv E sigma).bijective

/-! ## Model tests -/

/-- Model test at one relator cell.  `no_interiorEdge_of_rCellCount_one` shows
there are no interior edges there, so the edge type is empty and `Phi_M` has no
edges, whatever cyclic order is chosen. -/
theorem phiMap_edgeCount_of_isEmpty (E : Type v) [Fintype E] [IsEmpty E]
    (sigma : Equiv.Perm (E × Bool)) :
    (phiMap E sigma).edgeCount = 0 := by
  rw [phiMap_edgeCount]
  simp

/-- Model test at two relator cells joined by one selected region: `Phi_M` has
exactly one edge. -/
theorem phiMap_edgeCount_of_unique (E : Type v) [Fintype E] [Unique E]
    (sigma : Equiv.Perm (E × Bool)) :
    (phiMap E sigma).edgeCount = 1 := by
  rw [phiMap_edgeCount]
  simp

/-! ## Osin's condition (*) -/

/-- **Loops of `Phi_M` are already excluded.**  Osin writes "it is easy to show
that `Phi_M` can not contain loops either"; in this formalization that is not an
argument but a field, since `Contiguity.target_ne_source` says a relator-cell
target is a different cell. -/
theorem interiorEdge_source_ne_target
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    (edge : InteriorEdge selected) :
    edge.candidate.contiguity.source ≠ edge.target :=
  edge.candidate.contiguity.target_ne_source edge.target edge.target_eq

/-- **Simplicity of `Phi_M`: the multiple-edge half of Osin's condition (`*`).**
Two selected interior regions joining the same ordered pair of cells are the
same region.

Osin does *not* derive this from Definition `M`, and does not use a multigraph
Euler bound.  He assumes it, verbatim (arXiv math/0411039, `embed-final.tex`,
just after the definition of `Phi_M`):

> `(*)` For any distinguished system of `e`-contiguity subdiagrams `M` in
> `Delta`, the graph `Phi_M` is simple and inside every `2`-gon of `Phi'_M`,
> there is a vertex of `Phi_M`.

with the remark "The next `4` results are proved under the following additional
assumption.  It will be eliminated later in Lemma `65`."  Its elimination, in
Lemma `65(a)`, is an induction on the number of `R`-cells that consumes Lemma
`O52`, Lemma `Eul` and Lemma `62`: two distinguished subdiagrams between the
same pair bound a subdiagram which must contain a cell, and the inductive
`1 - 13 mu` estimate for that cell contradicts `O52`'s `2 mu` plus two
side-arc terms below `mu / 2`, since `1 - 13 mu > 3 mu` for `mu < 1/16`.

The `2`-gon half of `(*)` is the merge argument already formalized as
`ExteriorMergeAvailable`: "otherwise one can include the `e`-contiguity
subdiagrams corresponding to the edges `e` and `f` into a single
`e`-contiguity subdiagram, contrary to the definition of `M`." -/
def PhiSimple
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta)) : Prop :=
  ∀ e₁ e₂ : InteriorEdge selected,
    e₁.candidate.contiguity.source = e₂.candidate.contiguity.source →
      e₁.target = e₂.target → e₁ = e₂

/-! ## What remains: the cyclic order at each cell -/

/-- **The geometric input to the realization.**  A vertex rotation on the
incidence darts whose orbits are the cells, together with planarity and the
face-degree bound.  Reading the cyclic order off each cell's boundary walk and
transporting planarity from the disc is Osin's construction of `Phi_M`; it is
named here rather than guessed at. -/
def PhiVertexRotation (E : Type v) [Fintype E] (vertexCard : ℕ) : Prop :=
  ∃ sigma : Equiv.Perm (E × Bool),
    (phiMap E sigma).IsPlanar ∧
      (∀ face : (phiMap E sigma).Face,
        3 ≤ (phiMap E sigma).faceDegree face) ∧
      (phiMap E sigma).vertexCount = vertexCard

/-- The realization follows from the cyclic order at each cell.  Everything
else -- the dart type, the edge reversal, and the edge count -- is settled
above. -/
theorem interiorIncidencePlanarRealization_of_vertexRotation
    (hrotation : ∀ {G : Type u} [Group G] {Lambda : Type w}
      {D : GGT.RelGenSet G Lambda}
      {W : Set (List (GGT.RelLetter G Lambda))}
      {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
      (selected : Finset (Candidate D eps Delta))
      (vertices : Finset (Fin Delta.rCellCount))
      (edges : Finset (InteriorEdge selected)),
      EdgesCovered (InteriorEdge.Incident (selected := selected))
          vertices edges →
        vertices.Nonempty →
        PhiVertexRotation {e : InteriorEdge selected // e ∈ edges}
          vertices.card) :
    InteriorIncidencePlanarRealization.{u, w, v} := by
  intro G _ Lambda D W eps Delta selected vertices edges hcovered hnonempty
  obtain ⟨sigma, hplanar, hface, hvertex⟩ :=
    hrotation selected vertices edges hcovered hnonempty
  refine ⟨phiMap {e : InteriorEdge selected // e ∈ edges} sigma,
    hplanar, hface, hvertex, ?_⟩
  rw [phiMap_edgeCount]
  simp

end Embedded
end VanKampen
end GGT
end GroupApproximation
