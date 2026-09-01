import GroupApproximation.GGT.HullSCRelativeGreendlingerStatement
import GroupApproximation.GGT.HullSCLemma49PowerDiagram

/-!
# The correction step in Hull's Lemma 4.9

This file contains the part of Hull's proof which takes place after the
relative Greendlinger cell has been selected.  The two short sides and the
unexposed part of the cell form a detour around the exposed boundary arc.
The detour represents the same element modulo the normal closure of the
relator, and its relative norm is at most

`2 * eps + (unexposed cell length)`.

The remaining lemmas turn that local replacement into the two shortening
contradictions in Osin's proof of Lemma 6.3 (Hull's Lemma 4.9): an arc shorter
than one period is replaced inside a cyclic rotation of the shortest word;
an arc containing one period and a tail is replaced and the tail is read
backwards.  The long-arc branch is the prime-piece branch and is kept out of
this algebraic module.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

/-! ## Splitting a relative word under its value map -/

/-- A decomposition of the image of a list lifts to a decomposition of the
source list.  No injectivity of the map is needed: the lengths of the two
image prefixes determine the cuts. -/
theorem exists_three_split_of_map_eq_three_append
    {Alpha Beta : Type*} (f : Alpha → Beta)
    (word : List Alpha) (before middle after : List Beta)
    (h : word.map f = before ++ middle ++ after) :
    ∃ pre mid suf : List Alpha,
      word = pre ++ mid ++ suf ∧
      pre.map f = before ∧ mid.map f = middle ∧ suf.map f = after := by
  have two_split : ∀ (xs : List Alpha) (a b : List Beta),
      xs.map f = a ++ b →
        ∃ x y : List Alpha, xs = x ++ y ∧ x.map f = a ∧ y.map f = b := by
    intro xs a
    induction a generalizing xs with
    | nil =>
        intro b hab
        exact ⟨[], xs, by simp, rfl, by simpa using hab⟩
    | cons z zs ih =>
        intro b hab
        cases xs with
        | nil => simp at hab
        | cons x tail =>
            simp only [List.map_cons, List.cons_append, List.cons.injEq] at hab
            obtain ⟨hhead, htail⟩ := hab
            obtain ⟨p, q, hpq, hp, hq⟩ := ih tail b htail
            refine ⟨x :: p, q, ?_, ?_, hq⟩
            · rw [hpq, List.cons_append]
            · simp only [List.map_cons, hhead, hp]
  obtain ⟨pre, rest, hword, hpre, hrest⟩ :=
    two_split word before (middle ++ after) (by simpa only [List.append_assoc] using h)
  obtain ⟨mid, suf, hrestSplit, hmid, hsuf⟩ :=
    two_split rest middle after hrest
  exact ⟨pre, mid, suf, by rw [hword, hrestSplit, List.append_assoc],
    hpre, hmid, hsuf⟩

/-- The group-valued boundary decomposition in a relative Greendlinger
certificate therefore comes from an actual subword of the repeated relative
boundary word. -/
theorem exists_boundaryArc_source
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {boundary : List (GGT.RelLetter G Lambda)}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps
      (boundary.map GGT.RelLetter.val) relator) :
    ∃ pre arc suf : List (GGT.RelLetter G Lambda),
      boundary = pre ++ arc ++ suf ∧
      pre.map GGT.RelLetter.val = C.boundaryBefore ∧
      arc.map GGT.RelLetter.val = C.boundaryArc ∧
      suf.map GGT.RelLetter.val = C.boundaryAfter ∧
      GGT.RelLetter.listVal arc = C.boundaryArc.prod := by
  obtain ⟨pre, arc, suf, hsplit, hpre, harc, hsuf⟩ :=
    exists_three_split_of_map_eq_three_append GGT.RelLetter.val boundary
      C.boundaryBefore C.boundaryArc C.boundaryAfter C.boundary_decomposition
  refine ⟨pre, arc, suf, hsplit, hpre, harc, hsuf, ?_⟩
  show (arc.map GGT.RelLetter.val).prod = C.boundaryArc.prod
  rw [harc]

/-! ## The cell detour in the normal closure -/

/-- Every member of the one-relator symmetrized family has value in the
normal closure of the original relator value. -/
theorem listVal_mem_normalClosure_of_mem_symmetrized
    {G : Type u} [Group G] {Lambda : Type w}
    {v r : List (GGT.RelLetter G Lambda)}
    (hr : r ∈ RelWord.symmetrized v) :
    GGT.RelLetter.listVal r ∈
      Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G) := by
  rw [← RelWord.normalClosure_listVal_image_symmetrized v]
  exact Subgroup.subset_normalClosure ⟨r, hr, rfl⟩

/-- The detour around a boundary contiguity arc.  It is read from the first
connector backwards, then around the unexposed cell boundary, then through
the second connector backwards. -/
def RelativeBoundaryContiguity.detourValue
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator) : G :=
  (GGT.RelLetter.listVal C.leftSide)⁻¹ *
    (GGT.RelLetter.listVal C.remainder)⁻¹ *
      (GGT.RelLetter.listVal C.rightSide)⁻¹

/-- The exposed boundary arc and the cell detour have the same image modulo
any normal subgroup containing the relator value. -/
theorem RelativeBoundaryContiguity.arc_inv_mul_detour_mem
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (N : Subgroup G) [N.Normal]
    (hrelator : GGT.RelLetter.listVal relator ∈ N) :
    C.boundaryArc.prod⁻¹ * C.detourValue ∈ N := by
  have hwhole : GGT.RelLetter.listVal C.exterior *
      GGT.RelLetter.listVal C.remainder ∈ N := by
    rw [← RelWord.listVal_append, ← C.relator_decomposition]
    exact hrelator
  have hwholeInv := N.inv_mem hwhole
  let a : G := GGT.RelLetter.listVal C.leftSide * C.boundaryArc.prod
  have hconj := (inferInstance : N.Normal).conj_mem
    (GGT.RelLetter.listVal C.exterior *
      GGT.RelLetter.listVal C.remainder)⁻¹ hwholeInv a⁻¹
  have heq : a⁻¹ *
        (GGT.RelLetter.listVal C.exterior *
          GGT.RelLetter.listVal C.remainder)⁻¹ * (a⁻¹)⁻¹ =
      C.boundaryArc.prod⁻¹ * C.detourValue := by
    dsimp [a, RelativeBoundaryContiguity.detourValue]
    rw [C.exterior_value]
    group
  rw [heq] at hconj
  exact hconj

/-- The detour has the expected length bound: the two connectors cost at most
`eps` each, and the remainder is read literally. -/
theorem RelativeBoundaryContiguity.wordNorm_detourValue_le
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (hrelator : RelWord.IsAdmissible D relator) :
    wordNorm D.alphabet.carrier C.detourValue ≤
      2 * eps + C.remainder.length := by
  have hrem : RelWord.IsAdmissible D C.remainder := by
    intro x hx
    apply hrelator x
    rw [C.relator_decomposition]
    exact List.mem_append_right _ hx
  have hleft : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal C.leftSide) ≤ eps :=
    le_trans (GGT.OsinComponents.wordNorm_listVal_le D C.leftSide
      C.leftSide_admissible) C.leftSide_short
  have hright : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal C.rightSide) ≤ eps :=
    le_trans (GGT.OsinComponents.wordNorm_listVal_le D C.rightSide
      C.rightSide_admissible) C.rightSide_short
  have hmiddle : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal C.remainder) ≤ C.remainder.length :=
    GGT.OsinComponents.wordNorm_listVal_le D C.remainder hrem
  have hleftInv : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal C.leftSide)⁻¹ ≤ eps := by
    rw [wordNorm_inv D.alphabet.symmetricGenerating]
    exact hleft
  have hrightInv : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal C.rightSide)⁻¹ ≤ eps := by
    rw [wordNorm_inv D.alphabet.symmetricGenerating]
    exact hright
  have hmiddleInv : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal C.remainder)⁻¹ ≤ C.remainder.length := by
    rw [wordNorm_inv D.alphabet.symmetricGenerating]
    exact hmiddle
  have hmul₁ := wordNorm_mul_le D.alphabet.symmetricGenerating
    (GGT.RelLetter.listVal C.leftSide)⁻¹
    (GGT.RelLetter.listVal C.remainder)⁻¹
  have hmul₂ := wordNorm_mul_le D.alphabet.symmetricGenerating
    ((GGT.RelLetter.listVal C.leftSide)⁻¹ *
      (GGT.RelLetter.listVal C.remainder)⁻¹)
    (GGT.RelLetter.listVal C.rightSide)⁻¹
  dsimp only [RelativeBoundaryContiguity.detourValue]
  omega

/-! ## Replacing a subword modulo a normal subgroup -/

/-- Replacing a middle factor by an element equal to it modulo a normal
subgroup keeps the represented element in the same quotient-conjugacy class.
The normal correction is conjugated by the suffix. -/
theorem conjugateModulo_of_middle_replacement
    {G : Type u} [Group G] {Lambda : Type w}
    (N : Subgroup G) [N.Normal]
    (pre mid suf : List (GGT.RelLetter G Lambda)) (replacement : G)
    (hdefect : (GGT.RelLetter.listVal mid)⁻¹ * replacement ∈ N) :
    ConjugateModulo N (GGT.RelLetter.listVal (pre ++ mid ++ suf))
      (GGT.RelLetter.listVal pre * replacement *
        GGT.RelLetter.listVal suf) := by
  let k : G := (GGT.RelLetter.listVal suf)⁻¹ *
    ((GGT.RelLetter.listVal mid)⁻¹ * replacement) *
      GGT.RelLetter.listVal suf
  have hk : k ∈ N := by
    dsimp [k]
    simpa only [inv_inv] using
      (inferInstance : N.Normal).conj_mem
        ((GGT.RelLetter.listVal mid)⁻¹ * replacement) hdefect
        (GGT.RelLetter.listVal suf)⁻¹
  refine ⟨1, k, hk, ?_⟩
  rw [RelWord.listVal_append, RelWord.listVal_append]
  dsimp [k]
  group

/-- A genuinely shorter replacement inside a cyclic rotation contradicts
minimality in the quotient conjugacy class. -/
theorem false_of_short_cyclic_replacement
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (N : Subgroup G) [N.Normal]
    {g : G} (hshort : IsShortestModuloConjugacy D.alphabet.carrier N g)
    {word : List (GGT.RelLetter G Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D 1 g word)
    (m : ℕ) (hm : m ≤ word.length)
    (pre arc suf : List (GGT.RelLetter G Lambda))
    (hsplit : word.rotate m = pre ++ arc ++ suf)
    (replacement : G)
    (hdefect : (GGT.RelLetter.listVal arc)⁻¹ * replacement ∈ N)
    (hshorter : wordNorm D.alphabet.carrier replacement < arc.length) : False := by
  let rotated : G := GGT.RelLetter.listVal (word.rotate m)
  let candidate : G := GGT.RelLetter.listVal pre * replacement *
    GGT.RelLetter.listVal suf
  have hrotateConj : ConjugateModulo N g rotated := by
    let p : G := GGT.RelLetter.listVal (word.take m)
    refine ⟨p⁻¹, 1, N.one_mem, ?_⟩
    dsimp [rotated, p]
    rw [RelWord.listVal_rotate word hm]
    have hval : GGT.RelLetter.listVal word = g := by
      simpa using hword.2.1
    rw [hval]
    group
  have hreplace : ConjugateModulo N rotated candidate := by
    dsimp [rotated, candidate]
    rw [hsplit]
    exact conjugateModulo_of_middle_replacement N pre arc suf replacement hdefect
  have hcandConj : ConjugateModulo N g candidate := hrotateConj.trans hreplace
  have hrotLetters : RelWord.IsAdmissible D (word.rotate m) := by
    intro x hx
    exact hword.1 x (List.mem_rotate.mp hx)
  have hpre : RelWord.IsAdmissible D pre := by
    intro x hx
    apply hrotLetters x
    rw [hsplit]
    exact List.mem_append_left _ hx
  have hsuf : RelWord.IsAdmissible D suf := by
    intro x hx
    apply hrotLetters x
    rw [hsplit]
    exact List.mem_append_right _ (List.mem_append_right _ hx)
  have hpreNorm : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal pre) ≤ pre.length :=
    GGT.OsinComponents.wordNorm_listVal_le D pre hpre
  have hsufNorm : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal suf) ≤ suf.length :=
    GGT.OsinComponents.wordNorm_listVal_le D suf hsuf
  have hmul₁ := wordNorm_mul_le D.alphabet.symmetricGenerating
    (GGT.RelLetter.listVal pre) replacement
  have hmul₂ := wordNorm_mul_le D.alphabet.symmetricGenerating
    (GGT.RelLetter.listVal pre * replacement)
    (GGT.RelLetter.listVal suf)
  have hcandUpper : wordNorm D.alphabet.carrier candidate < word.length := by
    dsimp only [candidate]
    have hlength := congrArg List.length hsplit
    simp only [List.length_rotate, List.length_append] at hlength
    omega
  have hlower := hshort candidate hcandConj
  have hgeodesic : wordNorm D.alphabet.carrier g = word.length := by
    simpa [wordDist_one_left] using hword.2.2.symm
  rw [hgeodesic] at hlower
  omega

/-- The short-arc branch of Hull's proof.  Once the boundary arc is located
inside one cyclic period, the cell detour is too short and contradicts the
chosen representative's quotient-conjugacy minimality. -/
theorem false_of_contiguity_short_arc
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (N : Subgroup G) [N.Normal]
    {g : G} (hshort : IsShortestModuloConjugacy D.alphabet.carrier N g)
    {word relator : List (GGT.RelLetter G Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D 1 g word)
    {eps : ℕ} {boundaryWord : List G}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (hrelatorAdmissible : RelWord.IsAdmissible D relator)
    (hrelatorMem : GGT.RelLetter.listVal relator ∈ N)
    (arc : List (GGT.RelLetter G Lambda))
    (harcValue : GGT.RelLetter.listVal arc = C.boundaryArc.prod)
    (m : ℕ) (hm : m ≤ word.length)
    (pre suf : List (GGT.RelLetter G Lambda))
    (hsplit : word.rotate m = pre ++ arc ++ suf)
    (hdetourShort : 2 * eps + C.remainder.length < arc.length) : False := by
  apply false_of_short_cyclic_replacement D N hshort hword m hm pre arc suf
    hsplit C.detourValue
  · rw [harcValue]
    exact C.arc_inv_mul_detour_mem N hrelatorMem
  · exact lt_of_le_of_lt
      (C.wordNorm_detourValue_le hrelatorAdmissible) hdetourShort

/-- If the exposed arc is one cyclic period followed by a tail, the detour
followed by the inverse tail replaces the whole period. -/
theorem false_of_contiguity_one_period
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (N : Subgroup G) [N.Normal]
    {g : G} (hshort : IsShortestModuloConjugacy D.alphabet.carrier N g)
    {word relator : List (GGT.RelLetter G Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D 1 g word)
    {eps : ℕ} {boundaryWord : List G}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (hrelatorAdmissible : RelWord.IsAdmissible D relator)
    (hrelatorMem : GGT.RelLetter.listVal relator ∈ N)
    (m : ℕ) (hm : m ≤ word.length)
    (tail : List (GGT.RelLetter G Lambda))
    (harcValue : C.boundaryArc.prod =
      GGT.RelLetter.listVal (word.rotate m ++ tail))
    (htailAdmissible : RelWord.IsAdmissible D tail)
    (hdetourShort : 2 * eps + C.remainder.length + tail.length < word.length) :
    False := by
  let replacement : G := C.detourValue * (GGT.RelLetter.listVal tail)⁻¹
  have hqdefect :
      (GGT.RelLetter.listVal (word.rotate m ++ tail))⁻¹ *
        C.detourValue ∈ N := by
    rw [← harcValue]
    exact C.arc_inv_mul_detour_mem N hrelatorMem
  have hperiodDefect :
      (GGT.RelLetter.listVal (word.rotate m))⁻¹ * replacement ∈ N := by
    have hconj := (inferInstance : N.Normal).conj_mem _ hqdefect
      (GGT.RelLetter.listVal tail)
    have heq : GGT.RelLetter.listVal tail *
          ((GGT.RelLetter.listVal (word.rotate m ++ tail))⁻¹ *
            C.detourValue) * (GGT.RelLetter.listVal tail)⁻¹ =
        (GGT.RelLetter.listVal (word.rotate m))⁻¹ * replacement := by
      dsimp [replacement]
      rw [RelWord.listVal_append]
      group
    rw [heq] at hconj
    exact hconj
  have htailNorm : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal tail)⁻¹ ≤ tail.length := by
    rw [wordNorm_inv D.alphabet.symmetricGenerating]
    exact GGT.OsinComponents.wordNorm_listVal_le D tail htailAdmissible
  have hmul := wordNorm_mul_le D.alphabet.symmetricGenerating
    C.detourValue (GGT.RelLetter.listVal tail)⁻¹
  have hreplacementShort : wordNorm D.alphabet.carrier replacement < word.length := by
    dsimp only [replacement]
    have hdetour := C.wordNorm_detourValue_le hrelatorAdmissible
    omega
  exact false_of_short_cyclic_replacement D N hshort hword m hm
    [] (word.rotate m) [] (by simp) replacement hperiodDefect
    (by simpa using hreplacementShort)

/-! ## Model checks -/

/-- In the trivial group no strict cyclic shortening certificate can exist:
the geodesic word for the identity is empty. -/
theorem no_short_cyclic_replacement_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda)
    (N : Subgroup PUnit)
    {word : List (GGT.RelLetter PUnit Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D 1 1 word) : word = [] := by
  have hzero : word.length = 0 := by
    have h := hword.2.2
    simpa [wordDist_one_left] using h
  exact List.length_eq_zero_iff.mp hzero

end HullSC
end GroupApproximation
