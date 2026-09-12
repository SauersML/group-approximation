import GroupApproximation.GGT.SystolicDefs
import GroupApproximation.GGT.VanKampen.CombMapStars
import GroupApproximation.Meta.AxiomGuard

/-!
# Minimal disc diagrams in a triangle complex

A closed edge path in a simply connected triangle complex `X` bounds a disc diagram: a
planar combinatorial map whose inner faces are triangles of `X`.  Among such diagrams
take one with the fewest triangles.  If two triangles sharing an interior edge had the
same third vertex in `X`, they could be folded away, so a least diagram has none.  Around
an interior vertex the corners then read a closed walk in the link of its image that
never turns straight back, and a large link forces a large degree.  That is the input of
the combinatorial Gauss--Bonnet count behind Caprace--Conder--Kaluba--Witzel's Theorem 3.1:
the triangle complex of `GHB(7)` has links of girth `6`, `8` and `8`.

## Vocabulary

* `LinksLargeAt X n`: the link of `v` (neighbours of `v`, joined when they span a triangle
  with `v`) has no closed nodup cycle of length `3 ≤ k < n v`.
* `TriangulatedDisc X γ`: a planar map with an outer face, a vertex labelling into `X`
  sending darts to edges, every inner face a triangle of `X` in rotation order, and the
  outer face read from a base dart spelling `γ`.
* `FillingStatement X` (HC4): every nonconstant closed edge path bounds a disc.
* `MirrorFoldStatement X` (HC6): a mirror pair of inner triangles folds away, removing at
  least two triangles and keeping the boundary.
* The four boundary constructors of HC3, consumed by HC4.

## Results

* HC1 `vertexCount_add_innerFaceCount`, `faceDegree_eq_three`, `two_mul_edgeCount`.
* HC5 `exists_least`.
* HC7 `third_ne_of_least`.
* HC8 `tri_linkVertex`, `adj_linkVertex`, `third_linkDart_succ`, `third_alpha_linkDart`,
  `linkVertex_periodic`.
* HC9 `exists_nodup_cycle_of_nonbacktracking`.
* HC10 `le_vertexDegree_of_least`, `exists_leastDisc_typedLinks`.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route (hyperbolicity of `GHB(7)`); certifies no manuscript step on its
own.
-/

namespace GroupApproximation
namespace Systolic

open GGT.VanKampen

universe u

variable {V : Type u}

/-! ## Typed link largeness -/

/-- **Typed link largeness**: the link of `v` has no closed nodup cycle of length `k` with
`3 ≤ k < n v`. -/
def LinksLargeAt (X : TriangleComplex V) (n : V → ℕ) : Prop :=
  ∀ (v : V) (c : List V), 3 ≤ c.length → c.length < n v → c.Nodup →
    (∀ x ∈ c, X.G.Adj v x) → ¬ List.IsChain (X.Tri v) (c ++ c.take 1)

/-- Large links at every vertex bound give 6-large links. -/
theorem linksSixLarge_of_linksLargeAt {X : TriangleComplex V} {n : V → ℕ}
    (hL : LinksLargeAt X n) (h6 : ∀ v, 6 ≤ n v) : LinksSixLarge X := by
  intro v c h3 h5 hnd hadj
  have hv := h6 v
  exact hL v c h3 (by omega) hnd hadj

/-- A triangle has three distinct vertices; in particular its last two differ. -/
theorem TriangleComplex.not_tri_eq_right (X : TriangleComplex V) {x y : V} :
    ¬ X.Tri x y y := by
  intro h
  exact X.G.irrefl (X.tri_adj h).2.1

/-! ## Permutation bookkeeping -/

theorem perm_pow_two_apply {α : Type*} (f : Equiv.Perm α) (x : α) :
    (f ^ 2) x = f (f x) := by
  rw [pow_two, Equiv.Perm.mul_apply]

theorem perm_pow_three_apply {α : Type*} (f : Equiv.Perm α) (x : α) :
    (f ^ 3) x = f (f (f x)) := by
  rw [pow_succ, Equiv.Perm.mul_apply, perm_pow_two_apply]

theorem facePerm_apply (M : CombMap.{0}) (d : M.Dart) :
    M.facePerm d = M.sigma (M.alpha d) :=
  rfl

/-- The face successor of a dart starts at the head of that dart. -/
theorem vertexOf_facePerm (M : CombMap.{0}) (d : M.Dart) :
    M.vertexOf (M.facePerm d) = M.vertexOf (M.alpha d) := by
  rw [facePerm_apply]
  exact M.vertexOf_sigma _

/-- Entering a vertex along `alpha d` and turning once gives `sigma d`. -/
theorem facePerm_alpha (M : CombMap.{0}) (d : M.Dart) :
    M.facePerm (M.alpha d) = M.sigma d := by
  rw [facePerm_apply, M.alpha_involutive d]

/-- Every vertex of a map has positive degree. -/
theorem vertexDegree_pos (M : CombMap.{0}) (d : M.Dart) :
    0 < M.vertexDegree (M.vertexOf d) := by
  have : Nonempty {e : M.Dart // (Quotient.mk'' e : CombMap.Orbit M.sigma) = M.vertexOf d} :=
    ⟨⟨d, rfl⟩⟩
  exact Nat.card_pos

/-! ## Disc diagrams -/

/-- **A triangulated disc in `X` bounding `γ`.**  A planar map with a distinguished outer
face.  Darts map to edges of `X`; the three darts of every inner face, in face rotation,
start at the three vertices of a triangle of `X`; the outer face, read from `base`, spells
the closed path `γ`. -/
structure TriangulatedDisc (X : TriangleComplex V) (γ : List V) where
  /-- The planar map. -/
  map : CombMap.{0}
  /-- The map is connected with Euler characteristic two. -/
  planar : map.IsPlanar
  /-- The exterior face. -/
  outer : map.Face
  /-- The vertex labelling. -/
  vtx : map.Vertex → V
  /-- Every dart maps to an edge of `X`. -/
  adj : ∀ d : map.Dart, X.G.Adj (vtx (map.vertexOf d)) (vtx (map.vertexOf (map.alpha d)))
  /-- Every inner face is a triangle of `X`. -/
  tri : ∀ d : map.Dart, map.faceOf d ≠ outer →
    (map.facePerm ^ 3) d = d ∧
      X.Tri (vtx (map.vertexOf d)) (vtx (map.vertexOf (map.facePerm d)))
        (vtx (map.vertexOf ((map.facePerm ^ 2) d)))
  /-- The dart from which the boundary is read. -/
  base : map.Dart
  base_outer : map.faceOf base = outer
  /-- The outer face read from `base` spells `γ`. -/
  boundary : List.ofFn (fun k : Fin (map.faceDegree outer + 1) =>
    vtx (map.vertexOf ((map.facePerm ^ (k : ℕ)) base))) = γ

namespace TriangulatedDisc

variable {X : TriangleComplex V} {γ : List V} (D : TriangulatedDisc X γ)

/-- The number of triangles. -/
noncomputable def innerFaceCount : ℕ := D.map.faceCount - 1

/-- The vertex of the face of `d` off the edge of `d`. -/
def third (d : D.map.Dart) : D.map.Vertex := D.map.vertexOf ((D.map.facePerm ^ 2) d)

/-- A vertex all of whose corners lie in inner faces. -/
def Interior (w : D.map.Vertex) : Prop :=
  ∀ d : D.map.Dart, D.map.vertexOf d = w → D.map.faceOf d ≠ D.outer

/-! ### HC1: counts -/

theorem one_le_faceCount : 1 ≤ D.map.faceCount := by
  have : Nonempty D.map.Face := ⟨D.outer⟩
  exact Nat.card_pos

/-- **Euler's formula for the disc**: `V + F = E + 1`, with `F` the triangles. -/
theorem vertexCount_add_innerFaceCount :
    D.map.vertexCount + D.innerFaceCount = D.map.edgeCount + 1 := by
  have h := D.map.euler_eq_two D.planar
  have hF := D.one_le_faceCount
  unfold innerFaceCount
  omega

/-- An inner face has exactly three darts. -/
theorem faceDegree_eq_three {d : D.map.Dart} (hd : D.map.faceOf d ≠ D.outer) :
    D.map.faceDegree (D.map.faceOf d) = 3 := by
  classical
  obtain ⟨h3, htri⟩ := D.tri d hd
  obtain ⟨h12, h23, h13⟩ := X.tri_adj htri
  have hne1 : D.map.facePerm d ≠ d := by
    intro h
    rw [h] at h12
    exact X.G.irrefl h12
  have hne2 : (D.map.facePerm ^ 2) d ≠ d := by
    intro h
    rw [h] at h13
    exact X.G.irrefl h13
  have hne12 : (D.map.facePerm ^ 2) d ≠ D.map.facePerm d := by
    intro h
    rw [h] at h23
    exact X.G.irrefl h23
  have e0 : (D.map.facePerm ^ (0 : ℕ)) d = d := by rw [pow_zero, Equiv.Perm.one_apply]
  have e1 : (D.map.facePerm ^ (1 : ℕ)) d = D.map.facePerm d := by rw [pow_one]
  let f : Fin 3 → {e : D.map.Dart //
      (Quotient.mk'' e : CombMap.Orbit D.map.facePerm) = D.map.faceOf d} :=
    fun t => ⟨(D.map.facePerm ^ (t : ℕ)) d, by
      change D.map.faceOf ((D.map.facePerm ^ (t : ℕ)) d) = D.map.faceOf d
      rw [D.map.faceOf_eq_iff]
      exact Equiv.Perm.sameCycle_pow_left.mpr (Equiv.Perm.SameCycle.refl _ _)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro s t hst
      have hval : (D.map.facePerm ^ (s : ℕ)) d = (D.map.facePerm ^ (t : ℕ)) d :=
        congrArg Subtype.val hst
      obtain ⟨s, hs⟩ := s
      obtain ⟨t, ht⟩ := t
      change (D.map.facePerm ^ s) d = (D.map.facePerm ^ t) d at hval
      simp only [Fin.mk.injEq]
      interval_cases s <;> interval_cases t
      · rfl
      · exact absurd (show D.map.facePerm d = d by rw [e0, e1] at hval; exact hval.symm) hne1
      · exact absurd (show (D.map.facePerm ^ 2) d = d by rw [e0] at hval; exact hval.symm) hne2
      · exact absurd (show D.map.facePerm d = d by rw [e1, e0] at hval; exact hval) hne1
      · rfl
      · exact absurd (show (D.map.facePerm ^ 2) d = D.map.facePerm d by
          rw [e1] at hval; exact hval.symm) hne12
      · exact absurd (show (D.map.facePerm ^ 2) d = d by rw [e0] at hval; exact hval) hne2
      · exact absurd (show (D.map.facePerm ^ 2) d = D.map.facePerm d by
          rw [e1] at hval; exact hval) hne12
      · rfl
    · rintro ⟨e, he⟩
      have hcyc : D.map.facePerm.SameCycle d e := by
        have he' : D.map.faceOf e = D.map.faceOf d := he
        exact ((D.map.faceOf_eq_iff e d).mp he').symm
      obtain ⟨i, hi⟩ := hcyc.exists_nat_pow_eq
      refine ⟨⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, Subtype.ext ?_⟩
      change (D.map.facePerm ^ (i % 3)) d = e
      have hq : (D.map.facePerm ^ (3 * (i / 3))) d = d := by
        rw [pow_mul]
        exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h3 _
      rw [← hi]
      conv_rhs => rw [← Nat.mod_add_div i 3, pow_add, Equiv.Perm.mul_apply, hq]
  change Nat.card {e : D.map.Dart //
    (Quotient.mk'' e : CombMap.Orbit D.map.facePerm) = D.map.faceOf d} = 3
  exact Nat.card_eq_of_equiv_fin (Equiv.ofBijective f hf).symm

/-- **Dart incidence**: `2E = 3F + B`, with `B` the outer face degree. -/
theorem two_mul_edgeCount :
    2 * D.map.edgeCount = 3 * D.innerFaceCount + D.map.faceDegree D.outer := by
  classical
  have hsum := D.map.sum_faceDegree_eq_two_mul_edgeCount
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ D.outer)] at hsum
  have hinner : ∀ f ∈ Finset.univ.erase D.outer, D.map.faceDegree f = 3 := by
    intro f hf
    have hne : f ≠ D.outer := Finset.ne_of_mem_erase hf
    have hrep : D.map.faceOf (Quotient.out f) = f := Quotient.out_eq f
    rw [← hrep] at hne ⊢
    exact D.faceDegree_eq_three hne
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ← Nat.card_eq_fintype_card] at hsum
  change D.map.faceDegree D.outer + (D.map.faceCount - 1) * 3 = 2 * D.map.edgeCount at hsum
  unfold innerFaceCount
  rw [← hsum]
  ring

/-! ### HC8: links of interior vertices -/

/-- The `k`-th dart around the vertex of `d₀`. -/
def linkDart (d₀ : D.map.Dart) (k : ℕ) : D.map.Dart := (D.map.sigma ^ k) d₀

/-- The head of the `k`-th dart around the vertex of `d₀`: the `k`-th link vertex. -/
def linkVertex (d₀ : D.map.Dart) (k : ℕ) : D.map.Vertex :=
  D.map.vertexOf (D.map.alpha (D.linkDart d₀ k))

theorem linkDart_succ (d₀ : D.map.Dart) (k : ℕ) :
    D.linkDart d₀ (k + 1) = D.map.sigma (D.linkDart d₀ k) := by
  unfold linkDart
  rw [pow_succ', Equiv.Perm.mul_apply]

theorem vertexOf_linkDart (d₀ : D.map.Dart) (k : ℕ) :
    D.map.vertexOf (D.linkDart d₀ k) = D.map.vertexOf d₀ := by
  induction k with
  | zero =>
    change D.map.vertexOf ((D.map.sigma ^ 0) d₀) = _
    rw [pow_zero, Equiv.Perm.one_apply]
  | succ k ih => rw [D.linkDart_succ, D.map.vertexOf_sigma, ih]

theorem facePerm_alpha_linkDart (d₀ : D.map.Dart) (k : ℕ) :
    D.map.facePerm (D.map.alpha (D.linkDart d₀ k)) = D.linkDart d₀ (k + 1) := by
  rw [facePerm_alpha, D.linkDart_succ]

/-- The rotation around a vertex returns after the vertex degree. -/
theorem linkDart_periodic (d₀ : D.map.Dart) (k : ℕ) :
    D.linkDart d₀ (k + D.map.vertexDegree (D.map.vertexOf d₀)) = D.linkDart d₀ k := by
  have hp : (D.map.sigma ^ D.map.vertexDegree (D.map.vertexOf d₀)) d₀ = d₀ :=
    D.map.pow_orbitDegree_apply d₀
  unfold linkDart
  rw [pow_add, Equiv.Perm.mul_apply, hp]

theorem linkVertex_periodic (d₀ : D.map.Dart) (k : ℕ) :
    D.linkVertex d₀ (k + D.map.vertexDegree (D.map.vertexOf d₀)) = D.linkVertex d₀ k := by
  unfold linkVertex
  rw [D.linkDart_periodic]

variable {D}

theorem linkDart_face_ne_outer {w : D.map.Vertex} (hw : D.Interior w) {d₀ : D.map.Dart}
    (hd₀ : D.map.vertexOf d₀ = w) (k : ℕ) : D.map.faceOf (D.linkDart d₀ k) ≠ D.outer :=
  hw _ ((D.vertexOf_linkDart d₀ k).trans hd₀)

theorem alpha_linkDart_face_ne_outer {w : D.map.Vertex} (hw : D.Interior w)
    {d₀ : D.map.Dart} (hd₀ : D.map.vertexOf d₀ = w) (k : ℕ) :
    D.map.faceOf (D.map.alpha (D.linkDart d₀ k)) ≠ D.outer := by
  rw [← D.map.faceOf_facePerm, D.facePerm_alpha_linkDart]
  exact linkDart_face_ne_outer hw hd₀ (k + 1)

/-- In the triangle on `alpha (e k)` and `e (k+1)`, the third dart closes back. -/
theorem facePerm_sq_linkDart_succ {w : D.map.Vertex} (hw : D.Interior w)
    {d₀ : D.map.Dart} (hd₀ : D.map.vertexOf d₀ = w) (k : ℕ) :
    (D.map.facePerm ^ 2) (D.linkDart d₀ (k + 1)) = D.map.alpha (D.linkDart d₀ k) := by
  have h3 := (D.tri (D.map.alpha (D.linkDart d₀ k)) (alpha_linkDart_face_ne_outer hw hd₀ k)).1
  rw [perm_pow_three_apply, D.facePerm_alpha_linkDart] at h3
  rw [perm_pow_two_apply]
  exact h3

/-- **The link walk**: consecutive link vertices of an interior vertex span a triangle with
it. -/
theorem tri_linkVertex {w : D.map.Vertex} (hw : D.Interior w) {d₀ : D.map.Dart}
    (hd₀ : D.map.vertexOf d₀ = w) (k : ℕ) :
    X.Tri (D.vtx w) (D.vtx (D.linkVertex d₀ k)) (D.vtx (D.linkVertex d₀ (k + 1))) := by
  have h := (D.tri (D.linkDart d₀ (k + 1)) (linkDart_face_ne_outer hw hd₀ (k + 1))).2
  rw [facePerm_sq_linkDart_succ hw hd₀ k, vertexOf_facePerm, D.vertexOf_linkDart, hd₀] at h
  exact X.tri_swap23 h

/-- Every link vertex is a neighbour. -/
theorem adj_linkVertex {w : D.map.Vertex} {d₀ : D.map.Dart} (hd₀ : D.map.vertexOf d₀ = w)
    (k : ℕ) : X.G.Adj (D.vtx w) (D.vtx (D.linkVertex d₀ k)) := by
  have h := D.adj (D.linkDart d₀ k)
  rw [D.vertexOf_linkDart, hd₀] at h
  exact h

/-- The third vertex of the triangle on `e (k+1)` is the previous link vertex. -/
theorem third_linkDart_succ {w : D.map.Vertex} (hw : D.Interior w) {d₀ : D.map.Dart}
    (hd₀ : D.map.vertexOf d₀ = w) (k : ℕ) :
    D.third (D.linkDart d₀ (k + 1)) = D.linkVertex d₀ k := by
  show D.map.vertexOf ((D.map.facePerm ^ 2) (D.linkDart d₀ (k + 1))) =
    D.map.vertexOf (D.map.alpha (D.linkDart d₀ k))
  rw [facePerm_sq_linkDart_succ hw hd₀ k]

/-- The third vertex of the triangle on `alpha (e k)` is the next link vertex. -/
theorem third_alpha_linkDart (d₀ : D.map.Dart) (k : ℕ) :
    D.third (D.map.alpha (D.linkDart d₀ k)) = D.linkVertex d₀ (k + 1) := by
  show D.map.vertexOf ((D.map.facePerm ^ 2) (D.map.alpha (D.linkDart d₀ k))) =
    D.map.vertexOf (D.map.alpha (D.linkDart d₀ (k + 1)))
  rw [perm_pow_two_apply, D.facePerm_alpha_linkDart, vertexOf_facePerm]

end TriangulatedDisc

/-! ## HC9: cycles in non-backtracking closed walks -/

/-- **A closed walk that never turns straight back contains a cycle.**  Take the shortest
window between two equal points: its points are distinct, it has at least three of them,
and it closes up. -/
theorem exists_nodup_cycle_of_nonbacktracking {α : Type*} {r : α → α → Prop}
    (hirr : ∀ x, ¬ r x x) {n : ℕ} (hn : 0 < n) (h : ℕ → α)
    (hper : ∀ k, h (k + n) = h k) (hadj : ∀ k, r (h k) (h (k + 1)))
    (hnb : ∀ k, h k ≠ h (k + 2)) :
    ∃ c : List α, 3 ≤ c.length ∧ c.length ≤ n ∧ c.Nodup ∧ (∀ x ∈ c, ∃ k, h k = x) ∧
      List.IsChain r (c ++ c.take 1) := by
  classical
  have hex : ∃ g, 0 < g ∧ ∃ i, h (i + g) = h i := ⟨n, hn, 0, hper 0⟩
  obtain ⟨g, ⟨hgpos, i, hi⟩, hmin⟩ : ∃ g, (0 < g ∧ ∃ i, h (i + g) = h i) ∧
      ∀ g' < g, ¬ (0 < g' ∧ ∃ i, h (i + g') = h i) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun g' hg' => Nat.find_min hex hg'⟩
  have hgle : g ≤ n := by
    by_contra hlt
    exact hmin n (by omega) ⟨hn, 0, hper 0⟩
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1] at hi
    have hr := hadj i
    rw [hi] at hr
    exact hirr _ hr
  have hg2 : g ≠ 2 := by
    intro h2
    rw [h2] at hi
    exact hnb i hi.symm
  have hg3 : 3 ≤ g := by omega
  refine ⟨(List.range g).map fun t => h (i + t), ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.length_map, List.length_range]
    exact hg3
  · rw [List.length_map, List.length_range]
    exact hgle
  · refine List.Nodup.map_on ?_ List.nodup_range
    intro s hs t ht hst
    rw [List.mem_range] at hs ht
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hmin (t - s) (by omega)
        ⟨by omega, i + s, by rw [show i + s + (t - s) = i + t by omega]; exact hst.symm⟩
    · exact hmin (s - t) (by omega)
        ⟨by omega, i + t, by rw [show i + t + (s - t) = i + s by omega]; exact hst⟩
  · intro x hx
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    exact ⟨i + t, rfl⟩
  · have htake : ((List.range g).map fun t => h (i + t)).take 1 = [h (i + g)] := by
      obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      rw [hi, List.range_succ_eq_map, List.map_cons]
      simp
    have hc : ((List.range g).map fun t => h (i + t)) ++
        ((List.range g).map fun t => h (i + t)).take 1 =
          (List.range g.succ).map fun t => h (i + t) := by
      rw [htake, List.range_succ, List.map_append, List.map_singleton]
    rw [hc]
    exact (List.isChain_map _).mpr ((List.isChain_range_succ _ g).mpr fun m _ => hadj (i + m))

/-! ## Named producers -/

section Statements

variable (X : TriangleComplex V)

/-- **HC3(a)**: gluing a triangle of `X` along a boundary edge. -/
def AttachTriangleStatement : Prop :=
  ∀ (p q : List V) (u v w : V), X.Tri u v w →
    TriangulatedDisc X (p ++ u :: w :: q) → Nonempty (TriangulatedDisc X (p ++ u :: v :: w :: q))

/-- **HC3(b)**: cutting off a triangle of `X` along two consecutive boundary edges. -/
def InsertChordStatement : Prop :=
  ∀ (p q : List V) (u v w : V), X.Tri u v w →
    TriangulatedDisc X (p ++ u :: v :: w :: q) → Nonempty (TriangulatedDisc X (p ++ u :: w :: q))

/-- **HC3(c)**: attaching a pendant edge at a boundary vertex. -/
def AttachPendantStatement : Prop :=
  ∀ (p q : List V) (u v : V), X.G.Adj u v →
    TriangulatedDisc X (p ++ u :: q) → Nonempty (TriangulatedDisc X (p ++ u :: v :: u :: q))

/-- **HC3(d)**: zipping a boundary backtrack. -/
def ZipSpurStatement : Prop :=
  ∀ (p q : List V) (u v : V),
    TriangulatedDisc X (p ++ u :: v :: u :: q) →
      Nonempty (TriangulatedDisc X (p ++ u :: q)) ∨ p ++ u :: q = [u]

/-- **HC4**: every nonconstant closed edge path bounds a triangulated disc. -/
def FillingStatement : Prop :=
  ∀ (v : V) (l : List V), List.IsChain X.G.Adj (v :: l ++ [v]) → l ≠ [] →
    Nonempty (TriangulatedDisc X (v :: l ++ [v]))

/-- **HC6**: a mirror pair of inner triangles folds away. -/
def MirrorFoldStatement : Prop :=
  ∀ (γ : List V) (D : TriangulatedDisc X γ) (d : D.map.Dart),
    D.map.faceOf d ≠ D.outer → D.map.faceOf (D.map.alpha d) ≠ D.outer →
    D.vtx (D.third d) = D.vtx (D.third (D.map.alpha d)) →
      ∃ D' : TriangulatedDisc X γ, D'.innerFaceCount + 2 ≤ D.innerFaceCount

end Statements

/-! ## HC5, HC7, HC10: least discs -/

variable {X : TriangleComplex V} {γ : List V}

/-- **HC5**: a disc with the fewest triangles. -/
theorem exists_least (hne : Nonempty (TriangulatedDisc X γ)) :
    ∃ D : TriangulatedDisc X γ, ∀ D' : TriangulatedDisc X γ,
      D.innerFaceCount ≤ D'.innerFaceCount := by
  classical
  have hex : ∃ k, ∃ D : TriangulatedDisc X γ, D.innerFaceCount = k := ⟨_, hne.some, rfl⟩
  obtain ⟨D, hD⟩ := Nat.find_spec hex
  refine ⟨D, fun D' => ?_⟩
  rw [hD]
  exact Nat.find_min' hex ⟨D', rfl⟩

/-- **HC7**: a least disc has no mirror pair. -/
theorem third_ne_of_least (hfold : MirrorFoldStatement X) {D : TriangulatedDisc X γ}
    (hmin : ∀ D' : TriangulatedDisc X γ, D.innerFaceCount ≤ D'.innerFaceCount)
    {d : D.map.Dart} (hd : D.map.faceOf d ≠ D.outer)
    (had : D.map.faceOf (D.map.alpha d) ≠ D.outer) :
    D.vtx (D.third d) ≠ D.vtx (D.third (D.map.alpha d)) := by
  intro heq
  obtain ⟨D', hD'⟩ := hfold γ D d hd had heq
  have h := hmin D'
  omega

/-- **An interior vertex of a least disc has degree at least its link bound.** -/
theorem le_vertexDegree_of_least (hfold : MirrorFoldStatement X) {n : V → ℕ}
    (hL : LinksLargeAt X n) {D : TriangulatedDisc X γ}
    (hmin : ∀ D' : TriangulatedDisc X γ, D.innerFaceCount ≤ D'.innerFaceCount)
    {w : D.map.Vertex} (hw : D.Interior w) : n (D.vtx w) ≤ D.map.vertexDegree w := by
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : D.map.Dart, D.map.vertexOf d₀ = w :=
    ⟨Quotient.out w, Quotient.out_eq w⟩
  subst hd₀
  have hpos := vertexDegree_pos D.map d₀
  obtain ⟨c, hc3, hcle, hnd, hmem, hchain⟩ :=
    exists_nodup_cycle_of_nonbacktracking (r := X.Tri (D.vtx (D.map.vertexOf d₀)))
      (fun x hx => X.not_tri_eq_right hx) hpos (fun k => D.vtx (D.linkVertex d₀ k))
      (fun k => congrArg D.vtx (D.linkVertex_periodic d₀ k))
      (fun k => TriangulatedDisc.tri_linkVertex hw rfl k)
      (fun k => by
        have hne := third_ne_of_least hfold hmin
          (TriangulatedDisc.linkDart_face_ne_outer hw rfl (k + 1))
          (TriangulatedDisc.alpha_linkDart_face_ne_outer hw rfl (k + 1))
        rw [TriangulatedDisc.third_linkDart_succ hw rfl k,
          TriangulatedDisc.third_alpha_linkDart d₀ (k + 1)] at hne
        exact hne)
  by_contra hlt
  have hlt' : D.map.vertexDegree (D.map.vertexOf d₀) < n (D.vtx (D.map.vertexOf d₀)) := by
    omega
  refine hL (D.vtx (D.map.vertexOf d₀)) c hc3 (by omega) hnd ?_ hchain
  intro x hx
  obtain ⟨k, rfl⟩ := hmem x hx
  exact TriangulatedDisc.adj_linkVertex rfl k

/-- **HC10: least discs with typed links.**  In a triangle complex with a filling producer
and a folding producer, every nonconstant closed edge path bounds a disc with the fewest
triangles, and every interior vertex of it has degree at least the link bound of its
image. -/
theorem exists_leastDisc_typedLinks (hfill : FillingStatement X) (hfold : MirrorFoldStatement X)
    {n : V → ℕ} (hL : LinksLargeAt X n) {v : V} {l : List V}
    (hl : List.IsChain X.G.Adj (v :: l ++ [v])) (hne : l ≠ []) :
    ∃ D : TriangulatedDisc X (v :: l ++ [v]),
      (∀ D' : TriangulatedDisc X (v :: l ++ [v]), D.innerFaceCount ≤ D'.innerFaceCount) ∧
      ∀ w : D.map.Vertex, D.Interior w → n (D.vtx w) ≤ D.map.vertexDegree w := by
  obtain ⟨D, hmin⟩ := exists_least (hfill v l hl hne)
  exact ⟨D, hmin, fun w hw => le_vertexDegree_of_least hfold hL hmin hw⟩

end Systolic
end GroupApproximation

open GroupApproximation.Systolic

#audit_axioms linksSixLarge_of_linksLargeAt
#audit_axioms TriangulatedDisc.vertexCount_add_innerFaceCount
#audit_axioms TriangulatedDisc.faceDegree_eq_three
#audit_axioms TriangulatedDisc.two_mul_edgeCount
#audit_axioms TriangulatedDisc.tri_linkVertex
#audit_axioms exists_nodup_cycle_of_nonbacktracking
#audit_axioms le_vertexDegree_of_least
#audit_axioms exists_leastDisc_typedLinks
