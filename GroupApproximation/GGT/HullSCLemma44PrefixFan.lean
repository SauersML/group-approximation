import GroupApproximation.GGT.HullSCLemma44PrefixPresentation
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Algebraic fans of prefix triangles

The prefix quotient turns every long Hull relator into a row of triangular
relations.  This file proves the telescoping identity for that row in the free
group on relative letters.  The result is quantitative: a relator of length
`n` is a product of `n` prefix triangles and `n` two-letter inverse cells.

This is the algebraic part of the bounded relative-presentation bridge.  It is
independent of a planar realization, so the same expansion can be used by the
relative isoperimetric consumer and by later diagram constructions.
-/

namespace GroupApproximation
namespace HullSC

universe u v w

/-! ## Relative words in a free group -/

/-- A relative word read as a positive word in the free group on all relative
letters. -/
def RelWord.freeVal
    {G : Type u} {Lambda : Type w}
    (word : List (GGT.RelLetter G Lambda)) :
    FreeGroup (GGT.RelLetter G Lambda) :=
  FreeGroup.mk (word.map fun a => (a, true))

@[simp] theorem RelWord.freeVal_nil
    {G : Type u} {Lambda : Type w} :
    RelWord.freeVal ([] : List (GGT.RelLetter G Lambda)) = 1 := rfl

@[simp] theorem RelWord.freeVal_cons
    {G : Type u} {Lambda : Type w}
    (a : GGT.RelLetter G Lambda)
    (word : List (GGT.RelLetter G Lambda)) :
    RelWord.freeVal (a :: word) =
      FreeGroup.of a * RelWord.freeVal word := by
  simp only [RelWord.freeVal, List.map_cons]
  rw [show FreeGroup.of a = FreeGroup.mk [(a, true)] by rfl,
    FreeGroup.mul_mk]
  rfl

@[simp] theorem RelWord.freeVal_singleton
    {G : Type u} {Lambda : Type w}
    (a : GGT.RelLetter G Lambda) :
    RelWord.freeVal [a] = FreeGroup.of a := by
  rw [RelWord.freeVal_cons, RelWord.freeVal_nil, mul_one]

theorem RelWord.freeVal_append
    {G : Type u} {Lambda : Type w}
    (left right : List (GGT.RelLetter G Lambda)) :
    RelWord.freeVal (left ++ right) =
      RelWord.freeVal left * RelWord.freeVal right := by
  induction left with
  | nil => simp
  | cons a left ih =>
      simp only [List.cons_append, RelWord.freeVal_cons, ih, mul_assoc]

/-- Evaluation of the positive free word agrees with `RelLetter.listVal`. -/
@[simp] theorem RelWord.lift_freeVal
    {G : Type u} [Group G] {Lambda : Type w}
    (word : List (GGT.RelLetter G Lambda)) :
    FreeGroup.lift GGT.RelLetter.val (RelWord.freeVal word) =
      GGT.RelLetter.listVal word := by
  induction word with
  | nil => rfl
  | cons a word ih =>
      rw [RelWord.freeVal_cons, map_mul, FreeGroup.lift_apply_of, ih,
        RelWord.listVal_cons]

/-- Mapping the free generators commutes with mapping a relative word. -/
@[simp] theorem RelWord.map_freeVal
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (q : G →* Q) (word : List (GGT.RelLetter G Lambda)) :
    FreeGroup.map (GGT.RelLetter.mapHom q) (RelWord.freeVal word) =
      RelWord.freeVal (word.map (GGT.RelLetter.mapHom q)) := by
  induction word with
  | nil => simp
  | cons a word ih =>
      simp only [RelWord.freeVal_cons, map_mul, FreeGroup.map.of, List.map_cons,
        ih]

/-! ## The telescoping fan -/

/-- Free-group value of one consecutive-prefix triangle. -/
def prefixTriangleFree
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (q : G →* Q) (pre : List (GGT.RelLetter G Lambda))
    (a : GGT.RelLetter G Lambda) :
    FreeGroup (GGT.RelLetter Q Lambda) :=
  RelWord.freeVal (GGT.RelGenSet.prefixTriangle q pre a)

/-- One triangle is the product of its two prefix generators and its middle
mapped letter. -/
theorem prefixTriangleFree_eq
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (q : G →* Q) (pre : List (GGT.RelLetter G Lambda))
    (a : GGT.RelLetter G Lambda) :
    prefixTriangleFree q pre a =
      FreeGroup.of
          (GGT.RelLetter.base (q (GGT.RelLetter.listVal pre))) *
        FreeGroup.of (GGT.RelLetter.mapHom q a) *
        FreeGroup.of
          (GGT.RelLetter.base
            (q (GGT.RelLetter.listVal (pre ++ [a])))⁻¹) := by
  simp only [prefixTriangleFree, GGT.RelGenSet.prefixTriangle,
    RelWord.freeVal_cons, RelWord.freeVal_nil, mul_one]
  rw [mul_assoc]

/-- The formal triangle in which the last prefix generator is inverted in the
free group.  This is the form that telescopes. -/
def idealPrefixTriangleFree
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (q : G →* Q) (pre : List (GGT.RelLetter G Lambda))
    (a : GGT.RelLetter G Lambda) :
    FreeGroup (GGT.RelLetter Q Lambda) :=
  FreeGroup.of
      (GGT.RelLetter.base (q (GGT.RelLetter.listVal pre))) *
    FreeGroup.of (GGT.RelLetter.mapHom q a) *
    (FreeGroup.of
      (GGT.RelLetter.base
        (q (GGT.RelLetter.listVal (pre ++ [a])))))⁻¹

/-- The two-letter identity word that identifies the positive letter named by
an inverse group element with the formal inverse of the original letter. -/
def prefixInversePair
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (q : G →* Q) (pre : List (GGT.RelLetter G Lambda))
    (a : GGT.RelLetter G Lambda) :
    List (GGT.RelLetter Q Lambda) :=
  [GGT.RelLetter.base (q (GGT.RelLetter.listVal (pre ++ [a]))),
    GGT.RelLetter.base
      (q (GGT.RelLetter.listVal (pre ++ [a])))⁻¹]

@[simp] theorem prefixInversePair_length
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (q : G →* Q) (pre : List (GGT.RelLetter G Lambda))
    (a : GGT.RelLetter G Lambda) :
    (prefixInversePair q pre a).length = 2 := rfl

@[simp] theorem prefixInversePair_value
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (q : G →* Q) (pre : List (GGT.RelLetter G Lambda))
    (a : GGT.RelLetter G Lambda) :
    GGT.RelLetter.listVal (prefixInversePair q pre a) = 1 := by
  simp only [prefixInversePair, RelWord.listVal_cons,
    GGT.RelLetter.listVal_nil]
  change q (GGT.RelLetter.listVal (pre ++ [a])) *
    ((q (GGT.RelLetter.listVal (pre ++ [a])))⁻¹ * 1) = 1
  group

/-- The literal prefix triangle is the telescoping formal triangle followed by
one two-letter inverse cell. -/
theorem prefixTriangleFree_eq_ideal_mul_inversePair
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (q : G →* Q) (pre : List (GGT.RelLetter G Lambda))
    (a : GGT.RelLetter G Lambda) :
    prefixTriangleFree q pre a =
      idealPrefixTriangleFree q pre a *
        RelWord.freeVal (prefixInversePair q pre a) := by
  rw [prefixTriangleFree_eq]
  simp only [idealPrefixTriangleFree, prefixInversePair,
    RelWord.freeVal_cons, RelWord.freeVal_nil, mul_one]
  group

/-! ## The bounded cell family -/

/-- The inverse-pair relations attached to displayed steps of relators. -/
def RelWord.prefixInversePairs
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (W : Set (List (GGT.RelLetter G Lambda))) (q : G →* Q) :
    Set (List (GGT.RelLetter Q Lambda)) :=
  {pair | ∃ word ∈ W, ∃ pre a suffix,
    word = pre ++ a :: suffix ∧ pair = prefixInversePair q pre a}

/-- Prefix triangles together with their two-letter inverse connectors. -/
def RelWord.prefixPresentationCells
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (W : Set (List (GGT.RelLetter G Lambda))) (q : G →* Q) :
    Set (List (GGT.RelLetter Q Lambda)) :=
  RelWord.prefixTriangles W q ∪ RelWord.prefixInversePairs W q

/-- The ordered row of prefix triangles for the letters of `suffix`, starting
at the displayed prefix `pre`. -/
def prefixTriangleFan
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (q : G →* Q) :
    List (GGT.RelLetter G Lambda) →
      List (GGT.RelLetter G Lambda) →
        List (FreeGroup (GGT.RelLetter Q Lambda))
  | _, [] => []
  | pre, a :: suffix =>
      idealPrefixTriangleFree q pre a ::
        prefixTriangleFan q (pre ++ [a]) suffix

@[simp] theorem prefixTriangleFan_nil
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (q : G →* Q) (pre : List (GGT.RelLetter G Lambda)) :
    prefixTriangleFan q pre [] = [] := rfl

@[simp] theorem prefixTriangleFan_cons
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (q : G →* Q) (pre : List (GGT.RelLetter G Lambda))
    (a : GGT.RelLetter G Lambda)
    (suffix : List (GGT.RelLetter G Lambda)) :
    prefixTriangleFan q pre (a :: suffix) =
      idealPrefixTriangleFree q pre a ::
        prefixTriangleFan q (pre ++ [a]) suffix := rfl

@[simp] theorem prefixTriangleFan_length
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (q : G →* Q) (pre suffix : List (GGT.RelLetter G Lambda)) :
    (prefixTriangleFan q pre suffix).length = suffix.length := by
  induction suffix generalizing pre with
  | nil => rfl
  | cons a suffix ih =>
      simp only [prefixTriangleFan_cons, List.length_cons, ih]

/-- The prefix-triangle fan telescopes to the mapped word between its endpoint
prefix generators. -/
theorem prefixTriangleFan_prod
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (q : G →* Q) (pre suffix : List (GGT.RelLetter G Lambda)) :
    (prefixTriangleFan q pre suffix).prod =
      FreeGroup.of
          (GGT.RelLetter.base (q (GGT.RelLetter.listVal pre))) *
        RelWord.freeVal (suffix.map (GGT.RelLetter.mapHom q)) *
        (FreeGroup.of
          (GGT.RelLetter.base
            (q (GGT.RelLetter.listVal (pre ++ suffix)))))⁻¹ := by
  induction suffix generalizing pre with
  | nil =>
      simp only [prefixTriangleFan_nil, List.prod_nil, List.map_nil,
        RelWord.freeVal_nil, List.append_nil]
      group
  | cons a suffix ih =>
      rw [prefixTriangleFan_cons, List.prod_cons]
      rw [idealPrefixTriangleFree,
        ih (pre ++ [a]), List.map_cons, RelWord.freeVal_cons]
      have hprefix :
          GGT.RelLetter.listVal (pre ++ a :: suffix) =
            GGT.RelLetter.listVal ((pre ++ [a]) ++ suffix) := by
        congr 1
        simp only [List.append_assoc, List.singleton_append]
      rw [hprefix]
      group

/-! ## Quantitative products of prefix cells -/

/-- A product of conjugates of prefix-triangle free words.  The natural index
counts the triangle cells. -/
inductive IsPrefixCellProduct
    {Q : Type v} [Group Q] {Lambda : Type w}
    (triangles : Set (List (GGT.RelLetter Q Lambda))) :
    ℕ → FreeGroup (GGT.RelLetter Q Lambda) → Prop
  | one : IsPrefixCellProduct triangles 0 1
  | cell {triangle : List (GGT.RelLetter Q Lambda)}
      (htriangle : triangle ∈ triangles) :
      IsPrefixCellProduct triangles 1 (RelWord.freeVal triangle)
  | inv {area : ℕ} {g : FreeGroup (GGT.RelLetter Q Lambda)} :
      IsPrefixCellProduct triangles area g →
        IsPrefixCellProduct triangles area g⁻¹
  | conj {area : ℕ} {g : FreeGroup (GGT.RelLetter Q Lambda)} :
      IsPrefixCellProduct triangles area g →
      ∀ c : FreeGroup (GGT.RelLetter Q Lambda),
        IsPrefixCellProduct triangles area (c * g * c⁻¹)
  | mul {leftArea rightArea : ℕ}
      {g h : FreeGroup (GGT.RelLetter Q Lambda)} :
      IsPrefixCellProduct triangles leftArea g →
      IsPrefixCellProduct triangles rightArea h →
        IsPrefixCellProduct triangles (leftArea + rightArea) (g * h)

namespace IsPrefixCellProduct

/-- Prefix-cell products lie in the normal closure of the free triangle
words. -/
theorem mem_normalClosure
    {Q : Type v} [Group Q] {Lambda : Type w}
    {triangles : Set (List (GGT.RelLetter Q Lambda))}
    {area : ℕ} {g : FreeGroup (GGT.RelLetter Q Lambda)}
    (h : IsPrefixCellProduct triangles area g) :
    g ∈ Subgroup.normalClosure (RelWord.freeVal '' triangles) := by
  induction h with
  | one => exact Subgroup.one_mem _
  | cell htriangle =>
      exact Subgroup.subset_normalClosure ⟨_, htriangle, rfl⟩
  | inv h ih => exact Subgroup.inv_mem _ ih
  | conj h c ih =>
      exact Subgroup.normalClosure_normal.conj_mem _ ih c
  | mul hleft hright ihleft ihright =>
      exact Subgroup.mul_mem _ ihleft ihright

/-- Multiplying a list of one-cell factors costs its list length. -/
theorem list_prod
    {Q : Type v} [Group Q] {Lambda : Type w}
    {triangles : Set (List (GGT.RelLetter Q Lambda))}
    (cells : List (FreeGroup (GGT.RelLetter Q Lambda)))
    (hcell : ∀ c ∈ cells,
      ∃ triangle ∈ triangles, c = RelWord.freeVal triangle) :
    IsPrefixCellProduct triangles cells.length cells.prod := by
  induction cells with
  | nil => exact IsPrefixCellProduct.one
  | cons c cells ih =>
      obtain ⟨triangle, htriangle, rfl⟩ := hcell c (by simp)
      have htail : ∀ d ∈ cells,
          ∃ triangle ∈ triangles, d = RelWord.freeVal triangle := by
        intro d hd
        exact hcell d (by simp [hd])
      simpa only [List.length_cons, List.prod_cons, Nat.add_comm] using
        (IsPrefixCellProduct.cell htriangle).mul (ih htail)

end IsPrefixCellProduct

/-! ## A long relator expanded into bounded cells -/

/-- One formal telescoping triangle is a product of its literal triangle and
the inverse of its two-letter connector. -/
theorem idealPrefixTriangle_isPrefixCellProduct
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (q : G →* Q) {word pre suffix : List (GGT.RelLetter G Lambda)}
    {a : GGT.RelLetter G Lambda}
    (hword : word ∈ W) (hsplit : word = pre ++ a :: suffix) :
    IsPrefixCellProduct (RelWord.prefixPresentationCells W q) 2
      (idealPrefixTriangleFree q pre a) := by
  have htriangle : GGT.RelGenSet.prefixTriangle q pre a ∈
      RelWord.prefixPresentationCells W q := by
    left
    exact ⟨word, hword, pre, a, suffix, hsplit, rfl⟩
  have hpair : prefixInversePair q pre a ∈
      RelWord.prefixPresentationCells W q := by
    right
    exact ⟨word, hword, pre, a, suffix, hsplit, rfl⟩
  have hliteral := IsPrefixCellProduct.cell htriangle
  have hconnector := (IsPrefixCellProduct.cell hpair).inv
  have hproduct := hliteral.mul hconnector
  have hrewrite : idealPrefixTriangleFree q pre a =
      prefixTriangleFree q pre a *
        (RelWord.freeVal (prefixInversePair q pre a))⁻¹ := by
    rw [prefixTriangleFree_eq_ideal_mul_inversePair]
    group
  rw [hrewrite]
  exact hproduct

/-- A displayed suffix fan costs two bounded cells per source letter. -/
theorem prefixTriangleFan_isPrefixCellProduct
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (q : G →* Q) {word pre suffix : List (GGT.RelLetter G Lambda)}
    (hword : word ∈ W) (hsplit : word = pre ++ suffix) :
    IsPrefixCellProduct (RelWord.prefixPresentationCells W q)
      (2 * suffix.length) (prefixTriangleFan q pre suffix).prod := by
  induction suffix generalizing pre with
  | nil =>
      simpa only [prefixTriangleFan_nil, List.prod_nil, List.length_nil,
        mul_zero] using
        (IsPrefixCellProduct.one :
          IsPrefixCellProduct (RelWord.prefixPresentationCells W q) 0 1)
  | cons a suffix ih =>
      have hhead := idealPrefixTriangle_isPrefixCellProduct q hword hsplit
      have hsplitTail : word = (pre ++ [a]) ++ suffix := by
        simpa only [List.append_assoc, List.singleton_append] using hsplit
      have htail := ih (pre := pre ++ [a]) hsplitTail
      have hproduct := hhead.mul htail
      rw [prefixTriangleFan_cons, List.prod_cons]
      have harea : 2 * (a :: suffix).length =
          2 + 2 * suffix.length := by
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
        rw [Nat.add_comm]
      rw [harea]
      exact hproduct

/-- If the quotient kills a relator value, its mapped free word costs two
bounded prefix cells per source letter. -/
theorem mappedRelator_isPrefixCellProduct
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (q : G →* Q) {word : List (GGT.RelLetter G Lambda)}
    (hword : word ∈ W)
    (hkill : q (GGT.RelLetter.listVal word) = 1) :
    IsPrefixCellProduct (RelWord.prefixPresentationCells W q)
      (2 * word.length)
      (RelWord.freeVal (word.map (GGT.RelLetter.mapHom q))) := by
  let endpoint : FreeGroup (GGT.RelLetter Q Lambda) :=
    FreeGroup.of (GGT.RelLetter.base (1 : Q))
  have hfan := prefixTriangleFan_isPrefixCellProduct q hword
    (pre := []) (suffix := word) rfl
  have hfanEq : (prefixTriangleFan q [] word).prod =
      endpoint * RelWord.freeVal
        (word.map (GGT.RelLetter.mapHom q)) * endpoint⁻¹ := by
    rw [prefixTriangleFan_prod]
    simp only [GGT.RelLetter.listVal_nil, map_one, List.nil_append, hkill,
      endpoint]
  have hconj := hfan.conj endpoint⁻¹
  rw [hfanEq] at hconj
  have hfree : endpoint⁻¹ *
        (endpoint * RelWord.freeVal
          (word.map (GGT.RelLetter.mapHom q)) * endpoint⁻¹) *
        (endpoint⁻¹)⁻¹ =
      RelWord.freeVal (word.map (GGT.RelLetter.mapHom q)) := by
    group
  rw [hfree] at hconj
  exact hconj

/-- Normal-closure form of the exact prefix-fan expansion. -/
theorem mappedRelator_mem_prefixPresentationClosure
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (q : G →* Q) {word : List (GGT.RelLetter G Lambda)}
    (hword : word ∈ W)
    (hkill : q (GGT.RelLetter.listVal word) = 1) :
    RelWord.freeVal (word.map (GGT.RelLetter.mapHom q)) ∈
      Subgroup.normalClosure
        (RelWord.freeVal '' RelWord.prefixPresentationCells W q) :=
  (mappedRelator_isPrefixCellProduct q hword hkill).mem_normalClosure

end HullSC
end GroupApproximation
