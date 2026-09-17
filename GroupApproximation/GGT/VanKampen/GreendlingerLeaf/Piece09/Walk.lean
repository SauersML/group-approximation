import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkChain
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 09: the two-arc pocket face set at a whole section

Target: `OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement`
(`Estimating/OsinPocketTwoArcSection.lean`), Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b),
the subdiagram `Γ_1` with `∂Γ_1 = s_1 t_1 s_2 t_2`, in the case of a section `q_j` spanning the whole
boundary of `Δ`.

## The mathematical proof

Let `Δ` be least-area, `S` a globally distinguished section family, `a ≠ b` two exterior regions of
the cell `Π_i` to section `j`, with section `j` spanning all of `∂Δ`.

1. *Clean copy.*  As in `sectionPocketFaceSetInput_of_residuals`, the closed residuals
   `RegionPairThickening.sectionPocketRegionsCopy` and `sectionPocketKeptCell` give an O-equivalent
   copy `X = S₄.diagram` with letter labels, exterior regions `x ≠ y` of `Π_{i'}` to section `j`, the
   landed walk `K` (`PocketWalk.exists_pocketFaceSet_of_exteriorAt`)
   `K.walk = y.left ++ (x.src ++ Gap ++ y.src)⁻¹ ++ x.right ++ β`, where `β = K.targetArc`, with `K`
   clean against the pair `(x, y)` and also against `(y, x)`, and a pocket face set `P` with
   `P.boundary.cycle = K.walk` in walk order.  Write `Pf = P.faces`, `Rx = x.1`,
   `L = x.leftSide`, `A = y.left ++ (Gap ++ y.src)⁻¹`, `xt = x.targetArc`,
   `Mid = x.src⁻¹ ++ x.right ++ xt`.  Then `K.walk = A ++ Mid ++ β'` where `β = xt ++ β'`, and the
   boundary cycle of `x` is `Mid ++ L`.

2. *The target arc of `x` is a proper prefix of `β`.*  Both arcs start at the same position and
   `x`'s arc is no longer.  It is strictly shorter: otherwise the last dart of `y`'s target arc lies in
   `x`'s target arc too, and its face lies in `x.1 ∩ y.1`, against the disjointness of the family.

3. *Cutting off `x`.*  Take the face set `F = Pf \ Rx`.  Since `Rx ⊆ Pf` (the source dart of `x` is a
   boundary dart of `P` pointing into `Rx`, and `Rx` is connected through darts not on the walk), and
   `L` is disjoint from the walk (clean sides), the boundary darts of `F` are exactly the darts of
   `N = A ++ L⁻¹ ++ β'`, without repetition:
   * a dart of `A` or `β'` bounds `Pf` and does not start in `Rx` (else it lies in `Mid` or `L`);
   * a dart `ℓ⁻¹` with `ℓ ∈ L` starts in `Pf \ Rx` (else `ℓ` would lie on the walk) and ends in `Rx`;
   * conversely a boundary dart of `F` whose reverse ends outside `Pf` lies on the walk but not in
     `Mid`; one whose reverse ends in `Rx` has reverse in `Mid` (impossible) or in `L`.
   (`Boundary.lean`, a pure statement over a combinatorial map.)

4. *Walk order.*  `A`, `Mid`, `β'` are consecutive stretches of the closed walk `K.walk`: `A` runs
   from `p` to `q`, `Mid` from `q` to `r`, `β'` from `r` to `p`.  The boundary of `x` is a closed walk
   `Mid ++ L`, and `Mid` is nonempty, so `L` runs from `r` to `q`, whence `L⁻¹` runs from `q` to `r`,
   and `N` is a closed walk from `p` to `p` (`Walk.lean`).

5. *Arcs.*  The new source arc is the suffix `Gap ++ y.src` of `K.sourceArc`, strictly shorter than
   the boundary of `Π_{i'}` because `x.src` is nonempty.  The new target arc is the suffix `β'` of
   `β`, starting at `x.start + |x.targetArc| ≥ cut j` and ending where `β` ends, `≤ cut (j + 1)`; it
   is strictly shorter than `β`, hence than `∂X` (`Arcs.lean`).  The sides are `y.left` and `L⁻¹`,
   both of length and value norm at most `ε`.

6. *Kept cell and exterior face.*  `F` omits the exterior face and the source cell because `Pf` does.
   The kept cell of `P` lies in `F`: the inner G-region of `x` avoids relator cells.  So
   `PocketFaceSet.ofBoundaryCycleOfNotMem` assembles the pocket face set on `X`.

This module: dart paths between vertices of a combinatorial map, and the conversions from and to
the `IsChain` form used by `PocketFaceSet.ClosedWalk` and `FaceSetBoundary.isChain_closes`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09

universe u

/-- **A dart path** from the vertex `a` to the vertex `b`: each dart starts where the previous one
ends. -/
def DartPath (M : CombMap.{u}) : M.Vertex → M.Vertex → List M.Dart → Prop
  | a, b, [] => a = b
  | a, b, d :: l => M.vertexOf d = a ∧ DartPath M (M.vertexOf (M.alpha d)) b l

theorem dartPath_nil (M : CombMap.{u}) (a b : M.Vertex) : DartPath M a b [] ↔ a = b :=
  Iff.rfl

theorem dartPath_cons (M : CombMap.{u}) (a b : M.Vertex) (d : M.Dart) (l : List M.Dart) :
    DartPath M a b (d :: l) ↔ M.vertexOf d = a ∧ DartPath M (M.vertexOf (M.alpha d)) b l :=
  Iff.rfl

/-- A path along a concatenation passes through an intermediate vertex. -/
theorem dartPath_append (M : CombMap.{u}) (l₁ l₂ : List M.Dart) :
    ∀ a b : M.Vertex, DartPath M a b (l₁ ++ l₂) ↔ ∃ c, DartPath M a c l₁ ∧ DartPath M c b l₂ := by
  induction l₁ with
  | nil =>
    intro a b
    rw [List.nil_append]
    constructor
    · intro h
      exact ⟨a, (dartPath_nil M a a).mpr rfl, h⟩
    · rintro ⟨c, hc, h⟩
      rw [dartPath_nil] at hc
      rw [hc]
      exact h
  | cons d l ih =>
    intro a b
    rw [List.cons_append, dartPath_cons, ih]
    constructor
    · rintro ⟨hd, c, h₁, h₂⟩
      exact ⟨c, (dartPath_cons M a c d l).mpr ⟨hd, h₁⟩, h₂⟩
    · rintro ⟨c, h₁, h₂⟩
      obtain ⟨hd, h₁'⟩ := (dartPath_cons M a c d l).mp h₁
      exact ⟨hd, c, h₁', h₂⟩

/-- A path of three stretches. -/
theorem dartPath_append3 (M : CombMap.{u}) {l₁ l₂ l₃ : List M.Dart} {a b c e : M.Vertex}
    (h₁ : DartPath M a b l₁) (h₂ : DartPath M b c l₂) (h₃ : DartPath M c e l₃) :
    DartPath M a e (l₁ ++ l₂ ++ l₃) :=
  (dartPath_append M (l₁ ++ l₂) l₃ a e).mpr
    ⟨c, (dartPath_append M l₁ l₂ a c).mpr ⟨b, h₁, h₂⟩, h₃⟩

/-- The reversed darts of a path run backwards. -/
theorem dartPath_reverse_map (M : CombMap.{u}) (l : List M.Dart) :
    ∀ a b : M.Vertex, DartPath M a b l → DartPath M b a (l.reverse.map M.alpha) := by
  induction l with
  | nil =>
    intro a b h
    rw [dartPath_nil] at h
    rw [List.reverse_nil, List.map_nil, dartPath_nil]
    exact h.symm
  | cons d l ih =>
    intro a b h
    rw [dartPath_cons] at h
    obtain ⟨hd, hl⟩ := h
    rw [List.reverse_cons, List.map_append, dartPath_append]
    refine ⟨M.vertexOf (M.alpha d), ih _ b hl, ?_⟩
    rw [List.map_cons, List.map_nil, dartPath_cons, dartPath_nil, M.alpha_involutive d]
    exact ⟨rfl, hd⟩

/-- A nonempty path starts at its first dart. -/
theorem dartPath_start (M : CombMap.{u}) :
    ∀ (l : List M.Dart) (a b : M.Vertex), DartPath M a b l → (hne : l ≠ []) →
      a = M.vertexOf (l.head hne)
  | [], _, _, _, hne => (hne rfl).elim
  | d :: l, a, b, h, _ => ((dartPath_cons M a b d l).mp h).1.symm

/-- A nonempty path ends where its last dart ends. -/
theorem dartPath_end (M : CombMap.{u}) :
    ∀ (l : List M.Dart) (a b : M.Vertex), DartPath M a b l → (hne : l ≠ []) →
      b = M.vertexOf (M.alpha (l.getLast hne))
  | [], _, _, _, hne => (hne rfl).elim
  | [d], a, b, h, _ => by
    obtain ⟨-, h2⟩ := (dartPath_cons M a b d []).mp h
    rw [List.getLast_singleton]
    exact ((dartPath_nil M _ b).mp h2).symm
  | d :: e :: l, a, b, h, _ => by
    obtain ⟨-, h2⟩ := (dartPath_cons M a b d (e :: l)).mp h
    rw [List.getLast_cons_cons]
    exact dartPath_end M (e :: l) _ b h2 (List.cons_ne_nil e l)

/-- A chain of darts is a path from its first dart to the end of its last dart. -/
theorem dartPath_of_isChain (M : CombMap.{u}) :
    ∀ (l : List M.Dart) (hne : l ≠ []),
      l.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) →
        DartPath M (M.vertexOf (l.head hne)) (M.vertexOf (M.alpha (l.getLast hne))) l
  | [], hne, _ => (hne rfl).elim
  | [d], _, _ => by
    rw [List.getLast_singleton]
    exact (dartPath_cons M _ _ d []).mpr ⟨rfl, (dartPath_nil M _ _).mpr rfl⟩
  | d :: e :: l, _, h => by
    rw [List.isChain_cons_cons] at h
    have h1 : M.vertexOf (M.alpha d) = M.vertexOf e := h.1
    have ih := dartPath_of_isChain M (e :: l) (List.cons_ne_nil e l) h.2
    rw [List.getLast_cons_cons]
    refine (dartPath_cons M _ _ d (e :: l)).mpr ⟨rfl, ?_⟩
    rw [h1]
    exact ih

/-- A path is a chain of darts. -/
theorem isChain_of_dartPath (M : CombMap.{u}) :
    ∀ (l : List M.Dart) (a b : M.Vertex), DartPath M a b l →
      l.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
  | [], _, _, _ => List.IsChain.nil
  | [d], _, _, _ => List.IsChain.singleton d
  | d :: e :: l, a, b, h => by
    obtain ⟨-, h2⟩ := (dartPath_cons M a b d (e :: l)).mp h
    have he := dartPath_start M (e :: l) _ b h2 (List.cons_ne_nil e l)
    rw [List.isChain_cons_cons]
    exact ⟨he, isChain_of_dartPath M (e :: l) _ b h2⟩

/-- A nonempty closed path is a closed walk in the form of `PocketFaceSet.ClosedWalk`. -/
theorem closedWalk_of_dartPath (M : CombMap.{u}) (l : List M.Dart) (a : M.Vertex)
    (h : DartPath M a a l) (hne : l ≠ []) :
    l.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) ∧
      M.vertexOf (M.alpha (l.getLast hne)) = M.vertexOf (l.head hne) :=
  ⟨isChain_of_dartPath M l a a h,
    (dartPath_end M l a a h hne).symm.trans (dartPath_start M l a a h hne)⟩

/-- A closed walk in the form of `FaceSetBoundary.isChain_closes` is a closed path. -/
theorem dartPath_of_isChain_closes (M : CombMap.{u}) (l : List M.Dart) (hne : l ≠ [])
    (h : l.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) ∧
      ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, M.vertexOf (M.alpha a) = M.vertexOf b) :
    DartPath M (M.vertexOf (l.head hne)) (M.vertexOf (l.head hne)) l := by
  have hp := dartPath_of_isChain M l hne h.1
  have hc := h.2 (l.getLast hne) (by rw [List.getLast?_eq_some_getLast hne]; exact Option.mem_some_self _)
    (l.head hne) (by rw [List.head?_eq_some_head hne]; exact Option.mem_some_self _)
  rw [hc] at hp
  exact hp

/-- Two paths along the same nonempty list have the same endpoints. -/
theorem dartPath_unique (M : CombMap.{u}) {l : List M.Dart} {a b a' b' : M.Vertex}
    (h : DartPath M a b l) (h' : DartPath M a' b' l) (hne : l ≠ []) : a = a' ∧ b = b' :=
  ⟨(dartPath_start M l a b h hne).trans (dartPath_start M l a' b' h' hne).symm,
    (dartPath_end M l a b h hne).trans (dartPath_end M l a' b' h' hne).symm⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.DartPath
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.dartPath_nil
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.dartPath_cons
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.dartPath_append
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.dartPath_append3
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.dartPath_start
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.dartPath_end
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.dartPath_of_isChain
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.isChain_of_dartPath
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.dartPath_reverse_map
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.closedWalk_of_dartPath
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.dartPath_of_isChain_closes
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.dartPath_unique
