import Mathlib.GroupTheory.GroupAction.Quotient
import GroupApproximation.Kazhdan.CCKWTitsMoves
import GroupApproximation.Kazhdan.CCKWLinkCycles

/-!
# The coset complex of `GHB(7)`

The Kac–Moody–Steinberg group `GHB(7)` of Caprace–Conder–Kaluba–Witzel (arXiv:2011.09276,
Theorem 1.3) is the fundamental group of the triangle of groups with vertex groups
`P₀ = ⟨a,b⟩`, `P₁ = ⟨c,b⟩`, `P₂ = ⟨c,a⟩`.  Its coset complex `cosetComplex` is the Tits coset
complex `CCKWTits.titsComplex (GHB 7) vertexGroup`: vertices are the cosets `gPᵢ`, vertices of
different types sharing a representative are adjacent, and three of pairwise different types
sharing a representative span a triangle.

This module records what CCKW Theorem 3.1(ii) uses of that complex:

* **the links** (`cosetComplex_linkCycles`): the link of a vertex of type `0` has no cycle of
  length below `6`, and the link of a vertex of type `1` or `2` has none below `8`, over the
  order bounds `|U₃(7)| ≤ 7³`, `|U₄(7)| ≤ 7⁴` (from `Kazhdan/CCKWLinkCycles.lean` and the typed
  girths of `Kazhdan/CCKWLinkGirthTyped.lean`);
* **the action** (`cosetAction`): `GHB(7)` acts on the complex by left multiplication, by
  graph automorphisms that preserve types and triangles;
* **fixed vertices** (`conj_mem_of_cosetAction_eq`): an element fixing the vertex `kPᵢ`
  satisfies `k⁻¹ g k ∈ Pᵢ`.
-/

namespace GroupApproximation
namespace KMSGroup
namespace CCKW

/-- The vertices of the coset complex of `GHB(7)`: cosets of the three vertex groups. -/
abbrev Vertex : Type := Σ i : Fin 3, GHB 7 ⧸ vertexGroup i

/-- **The coset complex of `GHB(7)`.** -/
def cosetComplex : Systolic.TriangleComplex Vertex :=
  CCKWTits.titsComplex (GHB 7) vertexGroup

/-- The coset complex with its types and representatives, as the link-cycle analysis needs it. -/
def cosetPoints : TypedPoints cosetComplex vertexGroup where
  type := Sigma.fst
  On k x := CCKWTits.Rep vertexGroup x k
  tri h := h
  mem_of_on hk hk' := CCKWTits.mem_of_rep_rep hk hk'
  on_eq hk hk' h := CCKWTits.eq_of_rep hk hk' h

/-! ## The links -/

/-- **The links of the coset complex of `GHB(7)`**: no link cycle of length below `6` at the
vertices of type `0`, and none below `8` at the vertices of types `1` and `2`. -/
theorem cosetComplex_linkCycles [Finite (U3 7)] [Finite (U4 7)]
    (h3 : Nat.card (U3 7) ≤ 7 ^ 3) (h4 : Nat.card (U4 7) ≤ 7 ^ 4) (v : Vertex) (c : List Vertex)
    (h3c : 3 ≤ c.length) (hlt : c.length < if v.1 = 0 then 6 else 8) (hnd : c.Nodup)
    (_hadj : ∀ x ∈ c, cosetComplex.G.Adj v x) :
    ¬ List.IsChain (cosetComplex.Tri v) (c ++ c.take 1) :=
  fun hch => linkCycles_ghb7 h3 h4 cosetPoints v c h3c hlt hnd hch

/-! ## The action by left multiplication -/

/-- Left multiplication on vertices: `g • kPᵢ = gkPᵢ`. -/
def smulVertex (g : GHB 7) (x : Vertex) : Vertex :=
  ⟨x.1, g • x.2⟩

theorem rep_smulVertex {g k : GHB 7} {x : Vertex} (h : CCKWTits.Rep vertexGroup x k) :
    CCKWTits.Rep vertexGroup (smulVertex g x) (g * k) := by
  show g • x.2 = (QuotientGroup.mk (g * k) : GHB 7 ⧸ vertexGroup x.1)
  rw [show x.2 = (QuotientGroup.mk k : GHB 7 ⧸ vertexGroup x.1) from h]
  rfl

theorem smulVertex_mul (g h : GHB 7) (x : Vertex) :
    smulVertex (g * h) x = smulVertex g (smulVertex h x) :=
  congrArg (Sigma.mk x.1) (mul_smul g h x.2)

theorem smulVertex_one (x : Vertex) : smulVertex 1 x = x := by
  obtain ⟨i, y⟩ := x
  simp only [smulVertex, one_smul]

theorem adj_smulVertex {g : GHB 7} {x y : Vertex} (h : cosetComplex.G.Adj x y) :
    cosetComplex.G.Adj (smulVertex g x) (smulVertex g y) := by
  obtain ⟨hne, k, hx, hy⟩ := h
  exact ⟨hne, g * k, rep_smulVertex hx, rep_smulVertex hy⟩

theorem tri_smulVertex {g : GHB 7} {x y z : Vertex} (h : cosetComplex.Tri x y z) :
    cosetComplex.Tri (smulVertex g x) (smulVertex g y) (smulVertex g z) := by
  obtain ⟨h12, h23, h13, k, hx, hy, hz⟩ := h
  exact ⟨h12, h23, h13, g * k, rep_smulVertex hx, rep_smulVertex hy, rep_smulVertex hz⟩

/-- **`GHB(7)` acts on its coset complex by graph automorphisms.** -/
def cosetAction : GHB 7 →* (cosetComplex.G ≃g cosetComplex.G) where
  toFun g :=
    { toFun := smulVertex g
      invFun := smulVertex g⁻¹
      left_inv := fun x => by rw [← smulVertex_mul, inv_mul_cancel, smulVertex_one]
      right_inv := fun x => by rw [← smulVertex_mul, mul_inv_cancel, smulVertex_one]
      map_rel_iff' := by
        intro x y
        refine ⟨fun h => ?_, adj_smulVertex (g := g)⟩
        have h' : cosetComplex.G.Adj (smulVertex g⁻¹ (smulVertex g x))
            (smulVertex g⁻¹ (smulVertex g y)) := adj_smulVertex h
        rwa [← smulVertex_mul, ← smulVertex_mul, inv_mul_cancel, smulVertex_one,
          smulVertex_one] at h' }
  map_one' := RelIso.ext fun x => smulVertex_one x
  map_mul' g h := RelIso.ext fun x => smulVertex_mul g h x

theorem cosetAction_apply (g : GHB 7) (x : Vertex) : cosetAction g x = smulVertex g x := rfl

theorem cosetAction_fst (g : GHB 7) (x : Vertex) : (cosetAction g x).1 = x.1 := rfl

/-- **The action preserves triangles.** -/
theorem tri_cosetAction (g : GHB 7) {x y z : Vertex} (h : cosetComplex.Tri x y z) :
    cosetComplex.Tri (cosetAction g x) (cosetAction g y) (cosetAction g z) :=
  tri_smulVertex h

/-- **A fixed vertex conjugates into its vertex group**: if `g` fixes the vertex `x` of type
`i`, then some conjugate `k⁻¹ g k` lies in `Pᵢ`. -/
theorem conj_mem_of_cosetAction_eq {g : GHB 7} {x : Vertex} (h : cosetAction g x = x) :
    ∃ k : GHB 7, k⁻¹ * g * k ∈ vertexGroup x.1 := by
  obtain ⟨k, hk⟩ := CCKWTits.exists_rep x
  refine ⟨k, ?_⟩
  have h1 : CCKWTits.Rep vertexGroup (cosetAction g x) (g * k) := rep_smulVertex hk
  rw [h] at h1
  have h2 := CCKWTits.mem_of_rep_rep hk h1
  simpa only [mul_assoc] using h2

end CCKW
end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.CCKW.cosetComplex_linkCycles
#audit_axioms GroupApproximation.KMSGroup.CCKW.tri_cosetAction
#audit_axioms GroupApproximation.KMSGroup.CCKW.conj_mem_of_cosetAction_eq
