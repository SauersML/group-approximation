import GroupApproximation.GGT.HullSCRelativeGreendlingerStatement
import GroupApproximation.GGT.HullSCLemma49PowerDiagram
import Mathlib.Data.List.PeriodicityLemma

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

/-! ## Periodic boundary bookkeeping -/

/-- Repetition preserves admissibility of the period word. -/
theorem isAdmissible_lemma49BoundaryPower
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {word : List (GGT.RelLetter G Lambda)}
    (hword : RelWord.IsAdmissible D word) :
    ∀ n : ℕ, RelWord.IsAdmissible D (lemma49BoundaryPower word n)
  | 0 => by simp [lemma49BoundaryPower, RelWord.IsAdmissible]
  | n + 1 => by
      intro a ha
      rw [lemma49BoundaryPower, List.mem_append] at ha
      exact ha.elim (hword a) (isAdmissible_lemma49BoundaryPower hword n a)

/-- The recursive power word agrees with the standard flattened list of
replicated blocks. -/
theorem lemma49BoundaryPower_eq_flatten_replicate
    {Alpha : Type*} (word : List Alpha) : ∀ n : ℕ,
    lemma49BoundaryPower word n = (List.replicate n word).flatten
  | 0 => by simp [lemma49BoundaryPower]
  | n + 1 => by
      rw [lemma49BoundaryPower, lemma49BoundaryPower_eq_flatten_replicate,
        List.replicate_succ, List.flatten_cons]

/-- A positive boundary power has the length of one period as a list period. -/
theorem hasPeriod_lemma49BoundaryPower
    {Alpha : Type*} (word : List Alpha) {n : ℕ} (hn : 0 < n) :
    List.HasPeriod (lemma49BoundaryPower word n) word.length := by
  rw [lemma49BoundaryPower_eq_flatten_replicate]
  show (List.replicate n word).flatten <+:
    List.take word.length (List.replicate n word).flatten ++
      (List.replicate n word).flatten
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hfront : (List.replicate (j + 1) word).flatten =
      word ++ (List.replicate j word).flatten := by
    rw [List.replicate_succ, List.flatten_cons]
  have hback : (List.replicate (j + 1) word).flatten =
      (List.replicate j word).flatten ++ word := by
    rw [List.replicate_succ', List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil]
  have hcomm : (List.replicate j word).flatten ++ word =
      word ++ (List.replicate j word).flatten := hback.symm.trans hfront
  rw [hfront, List.take_left, ← hfront, hback]
  refine ⟨word, ?_⟩
  calc
    ((List.replicate j word).flatten ++ word) ++ word =
        (word ++ (List.replicate j word).flatten) ++ word :=
      congrArg (fun z => z ++ word) hcomm
    _ = word ++ ((List.replicate j word).flatten ++ word) := by
      rw [List.append_assoc]

/-- A factor no longer than one period of a positive boundary power is a
prefix of a cyclic rotation of the period.  This is the exact rotation
bookkeeping used in Hull's short-arc case. -/
theorem exists_prefix_rotate_of_infix_lemma49BoundaryPower
    {Alpha : Type*} {word arc : List Alpha} {n : ℕ}
    (hn : 0 < n) (hword : word ≠ [])
    (harc : arc <:+: lemma49BoundaryPower word n)
    (hlen : arc.length ≤ word.length) :
    ∃ m, m < word.length ∧ arc <+: word.rotate m := by
  have hperiod := hasPeriod_lemma49BoundaryPower word hn
  have hwordLength : 0 < word.length := List.length_pos_of_ne_nil hword
  obtain ⟨before, after, hsplit⟩ := harc
  have hfit : before.length + arc.length ≤
      (lemma49BoundaryPower word n).length := by
    have h := congrArg List.length hsplit
    simp only [List.length_append] at h
    omega
  refine ⟨before.length % word.length,
    Nat.mod_lt _ hwordLength, ?_⟩
  rw [List.prefix_iff_getElem?]
  intro i hi
  have hiPower : before.length + i <
      (lemma49BoundaryPower word n).length := by omega
  have hleft : arc[i]? =
      (lemma49BoundaryPower word n)[before.length + i]? := by
    rw [← hsplit, List.getElem?_append_left (by simp; omega),
      List.getElem?_append_right (by omega)]
    simp
  have hmod : (i + before.length % word.length) % word.length =
      (before.length + i) % word.length := by
    rw [Nat.add_comm before.length i]
    conv_rhs => rw [Nat.add_mod]
    conv_lhs => rw [Nat.add_mod]
    simp
  have hright : (word.rotate (before.length % word.length))[i]? =
      (lemma49BoundaryPower word n)[(before.length + i) % word.length]? := by
    rw [List.getElem?_rotate (by omega), hmod]
    have htake : (lemma49BoundaryPower word n).take word.length = word := by
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
      rw [lemma49BoundaryPower]
      exact List.take_left
    let k := (before.length + i) % word.length
    have hk : k < word.length := Nat.mod_lt _ hwordLength
    calc
      word[k]? = ((lemma49BoundaryPower word n).take word.length)[k]? :=
        congrArg (fun z : List Alpha => z[k]?) htake.symm
      _ = (lemma49BoundaryPower word n)[k]? := by
        rw [List.getElem?_take_of_lt hk]
  rw [hright,
    ← List.hasPeriod_iff_forall_getElem?_mod.mp hperiod _ hiPower, ← hleft]
  exact List.getElem?_eq_getElem hi

/-- A factor at least one period long begins with a full cyclic rotation of
the period.  Its remaining letters are exposed as an explicit tail. -/
theorem exists_rotate_append_of_infix_lemma49BoundaryPower
    {Alpha : Type*} {word arc : List Alpha} {n : ℕ}
    (hn : 0 < n) (hword : word ≠ [])
    (harc : arc <:+: lemma49BoundaryPower word n)
    (hlen : word.length ≤ arc.length) :
    ∃ m tail, m < word.length ∧ arc = word.rotate m ++ tail ∧
      tail.length = arc.length - word.length := by
  have htakeInfix : arc.take word.length <:+:
      lemma49BoundaryPower word n :=
    (List.take_prefix word.length arc).isInfix.trans harc
  have htakeLength : (arc.take word.length).length = word.length :=
    List.length_take_of_le hlen
  obtain ⟨m, hm, hprefix⟩ :=
    exists_prefix_rotate_of_infix_lemma49BoundaryPower hn hword htakeInfix
      (by rw [htakeLength])
  have hrotateLength : (word.rotate m).length = word.length :=
    List.length_rotate word m
  have heq : arc.take word.length = word.rotate m := by
    exact hprefix.eq_of_length (by rw [htakeLength, hrotateLength])
  refine ⟨m, arc.drop word.length, hm, ?_, by simp⟩
  conv_lhs => rw [← List.take_append_drop word.length arc]
  rw [heq]

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
    simp only [List.mem_append]
    exact Or.inl (Or.inl hx)
  have hsuf : RelWord.IsAdmissible D suf := by
    intro x hx
    apply hrotLetters x
    rw [hsplit]
    simp only [List.mem_append]
    exact Or.inr hx
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

/-! ## Routing a literal power arc into the shortening cases -/

/-- A certificate arc no longer than one period is automatically located in
one cyclic rotation, so the short-arc correction applies without any further
position hypothesis. -/
theorem false_of_contiguity_arc_le_period
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (N : Subgroup G) [N.Normal]
    {g : G} (hshort : IsShortestModuloConjugacy D.alphabet.carrier N g)
    {word relator arc : List (GGT.RelLetter G Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D 1 g word)
    {n eps : ℕ} (hn : 0 < n)
    (harcInfix : arc <:+: lemma49BoundaryPower word n)
    (harcLength : arc.length ≤ word.length)
    {boundaryWord : List G}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (hrelatorAdmissible : RelWord.IsAdmissible D relator)
    (hrelatorMem : GGT.RelLetter.listVal relator ∈ N)
    (harcValue : GGT.RelLetter.listVal arc = C.boundaryArc.prod)
    (hdetourShort : 2 * eps + C.remainder.length < arc.length) : False := by
  have hwordNe : word ≠ [] := by
    intro hnil
    rw [hnil, List.length_nil] at harcLength
    omega
  obtain ⟨m, hm, hprefix⟩ :=
    exists_prefix_rotate_of_infix_lemma49BoundaryPower hn hwordNe
      harcInfix harcLength
  obtain ⟨suf, hsuf⟩ := hprefix
  apply false_of_contiguity_short_arc D N hshort hword C
    hrelatorAdmissible hrelatorMem arc harcValue m (le_of_lt hm) [] suf
  · simpa only [List.nil_append] using hsuf.symm
  · exact hdetourShort

/-- A certificate arc at least one period long automatically begins with a
cyclic rotation of the period.  If the detour plus the remaining tail is
shorter than the period, the one-period correction applies. -/
theorem false_of_contiguity_period_le_arc
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (N : Subgroup G) [N.Normal]
    {g : G} (hshort : IsShortestModuloConjugacy D.alphabet.carrier N g)
    {word relator arc : List (GGT.RelLetter G Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D 1 g word)
    {n eps : ℕ} (hn : 0 < n) (hwordNe : word ≠ [])
    (harcInfix : arc <:+: lemma49BoundaryPower word n)
    (harcLength : word.length ≤ arc.length)
    {boundaryWord : List G}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (hrelatorAdmissible : RelWord.IsAdmissible D relator)
    (hrelatorMem : GGT.RelLetter.listVal relator ∈ N)
    (harcValue : GGT.RelLetter.listVal arc = C.boundaryArc.prod)
    (hdetourTailShort :
      2 * eps + C.remainder.length + (arc.length - word.length) <
        word.length) : False := by
  obtain ⟨m, tail, hm, hsplit, htailLength⟩ :=
    exists_rotate_append_of_infix_lemma49BoundaryPower hn hwordNe
      harcInfix harcLength
  have htailAdmissible : RelWord.IsAdmissible D tail := by
    intro a ha
    apply isAdmissible_lemma49BoundaryPower hword.1 n a
    obtain ⟨before, after, hpower⟩ := harcInfix
    rw [← hpower, hsplit]
    simp only [List.mem_append]
    tauto
  apply false_of_contiguity_one_period D N hshort hword C
    hrelatorAdmissible hrelatorMem m (le_of_lt hm) tail
  · rw [← harcValue, hsplit]
  · exact htailAdmissible
  · rwa [htailLength]

/-! ## Turning two close relator subwords into a prime piece -/

/-- Two disjoint subwords of one relator whose values differ by short
connectors are exactly a published prime piece.  The orientation may agree or
be reversed, matching the two alternatives in Hull's definition. -/
theorem isPrimePiece_of_disjoint_close_subwords
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {relator first middle second tail :
      List (GGT.RelLetter G Lambda)}
    (hrelator : relator ∈ W)
    (hsplit : relator = first ++ middle ++ second ++ tail)
    {left right : G}
    (hleft : wordNorm D.alphabet.carrier left ≤ eps)
    (hright : wordNorm D.alphabet.carrier right ≤ eps)
    (hvalue : GGT.RelLetter.listVal second =
        left * GGT.RelLetter.listVal first * right ∨
      GGT.RelLetter.listVal second =
        left * (GGT.RelLetter.listVal first)⁻¹ * right) :
    RelWord.IsPrimePiece D W eps first second relator := by
  exact ⟨hrelator, middle, tail, hsplit, left, right,
    hleft, hright, hvalue⟩

/-- Under Hull's `C₁` input, two such subwords cannot both have length at
least `mu` times the relator perimeter. -/
theorem false_of_two_large_close_relator_subwords
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hinput : RelWord.IsLemma49Input D W eps mu rho)
    {relator first middle second tail :
      List (GGT.RelLetter G Lambda)}
    (hrelator : relator ∈ W)
    (hsplit : relator = first ++ middle ++ second ++ tail)
    {left right : G}
    (hleft : wordNorm D.alphabet.carrier left ≤ eps)
    (hright : wordNorm D.alphabet.carrier right ≤ eps)
    (hvalue : GGT.RelLetter.listVal second =
        left * GGT.RelLetter.listVal first * right ∨
      GGT.RelLetter.listVal second =
        left * (GGT.RelLetter.listVal first)⁻¹ * right)
    (hfirst : mu * (relator.length : ℝ) ≤ (first.length : ℝ))
    (_hsecond : mu * (relator.length : ℝ) ≤ (second.length : ℝ)) : False := by
  have hpiece := isPrimePiece_of_disjoint_close_subwords hrelator hsplit
    hleft hright hvalue
  have hsmall := hinput.primePiecesSmall first second relator hpiece
  have hmax : mu * (relator.length : ℝ) ≤
      max (first.length : ℝ) (second.length : ℝ) :=
    le_trans hfirst (le_max_left _ _)
  have hmaxSecond : mu * (relator.length : ℝ) ≤
      max (first.length : ℝ) (second.length : ℝ) :=
    le_trans _hsecond (le_max_right _ _)
  linarith [hmax, hmaxSecond]

/-! ## Model checks -/

/-- In the trivial group no strict cyclic shortening certificate can exist:
the geodesic word for the identity is empty. -/
theorem no_short_cyclic_replacement_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda)
    (N : Subgroup PUnit)
    {word : List (GGT.RelLetter PUnit Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D 1 1 word) : word = [] := by
  have hzero : word.length = 0 :=
    hword.2.2.trans (wordDist_self D.alphabet.carrier (1 : PUnit))
  exact List.length_eq_zero_iff.mp hzero

end HullSC
end GroupApproximation
