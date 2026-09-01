import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyCompose
import GroupApproximation.GGT.HullSCRelatorSeparation2ExactCount
import GroupApproximation.GGT.HullSCPublishedSmallCancellation

/-!
# Published piece estimates for one exact Hull relator

The ordinary separation theorem historically hid the fixed-list argument
behind a producer and stated its conclusion only for syntactically distinct
members of the symmetrized family.  Hull's published same-word pieces and
primepieces need the argument one level lower: at one jointly chosen exact
design, before imposing any distinct-word exclusion.

This file first exposes that fixed-list quadrilateral conclusion.  The same
word estimate is then its immediate diagonal consequence: a long matched
prefix would give exactly the full-word conjugacy which the definition of a
published same-word piece excludes.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section FixedDesign

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

omit [Group G] in
/-- Rotating a four-part cyclic decomposition to the third part. -/
theorem rotate_four_append_to_third {T : Type*} (u middle u' tail : List T) :
    (u ++ middle ++ u' ++ tail).rotate (u.length + middle.length) =
      u' ++ tail ++ u ++ middle := by
  have h : ((u ++ middle) ++ (u' ++ tail)).rotate (u ++ middle).length =
      (u' ++ tail) ++ (u ++ middle) := by
    rw [List.rotate_eq_drop_append_take (by simp),
      List.drop_append_of_le_length (le_refl _), List.drop_length,
      List.take_append_of_le_length (le_refl _), List.take_length]
    simp
  simpa only [List.length_append, List.append_assoc] using h

omit [Group G] in
/-- Rotating a two-part decomposition to its second part. -/
theorem rotate_append_to_second {T : Type*} (first second : List T) :
    (first ++ second).rotate first.length = second ++ first := by
  rw [List.rotate_eq_drop_append_take (by simp),
    List.drop_append_of_le_length (le_refl _), List.drop_length,
    List.take_append_of_le_length (le_refl _), List.take_length]
  simp

/-- **The first occurrence in a direct prime match is uniformly short.**

The second occurrence is made a prefix by rotating the same cyclic word.  A
matched block then has the same exponent at both occurrences, hence the same
cyclic position.  Since the occurrences are disjoint, the position identity
has no wrap ambiguity; connector pinning bounds the intervening shift. -/
theorem directPrimeSource_length_le_of_exactDesign_rotate
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N)
    {epsD Cm designRho diffRadius W target : ℕ}
    {baseLetter : G} (hbase : baseLetter ∈ E.rel.base) {eps : ℕ}
    {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hCm : Cm * 4 ≤ designRho)
    (hpair : GGT.OsinComponents.MatchedPairOutput E.rel epsD
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hmatch : GGT.OsinComponents.DeepMatchOutput E.rel Cm
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hmsfive : 5 ≤ ms.length)
    {c : ℕ} {u middle u' tail : List (GGT.RelLetter G Bool)}
    (hsplit :
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms).rotate c =
        u ++ middle ++ u' ++ tail)
    {y z : G} (hy : wordNorm E.rel.base y ≤ eps)
    (hz : wordNorm E.rel.base z ≤ eps)
    (hval : GGT.RelLetter.listVal u' = y * GGT.RelLetter.listVal u * z) :
    u.length ≤ eps + 2 + blockConst [baseLetter] (max 1 (eps + 2)) := by
  let cw := max 1 (eps + 2)
  by_cases hshortu : u.length ≤ [baseLetter].length + 4
  · simp only [blockConst, List.length_singleton] at hshortu ⊢
    omega
  have hlong : [baseLetter].length + 4 < u.length := by omega
  let shift := u.length + middle.length
  let R := relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms
  have hu : R.rotate c = u ++ (middle ++ u' ++ tail) := by
    simpa only [R, List.append_assoc] using hsplit
  have hu' : R.rotate (c + shift) = u' ++ (tail ++ u ++ middle) := by
    rw [← List.rotate_rotate]
    rw [hu]
    simpa only [shift, List.append_assoc] using
      rotate_four_append_to_third u middle u' tail
  have huLen : u.length ≤ R.length := by
    have h := congrArg List.length hu
    rw [List.length_rotate, List.length_append] at h
    omega
  have hu'Len : u'.length ≤ R.length := by
    have h := congrArg List.length hu'
    rw [List.length_rotate, List.length_append] at h
    omega
  have hsymm : ∀ g ∈ E.rel.base, g⁻¹ ∈ E.rel.base :=
    fun g hg => (isSymmetricGeneratingSet_base₂ E).inv_mem g hg
  have hloxfam : ∀ b : Bool, E.lox b ∈ E.rel.fam b := by
    intro b
    rw [E.fam_eq]
    exact E.lox_mem b
  have hdisj : ∀ x : G, x ∈ E.rel.fam false → x ∈ E.rel.fam true → x = 1 := by
    rw [E.fam_eq]
    exact E.disjoint
  have hshort : eps + 2 ≤ blockConst [baseLetter] cw := by
    show eps + 2 ≤ [baseLetter].length + cw
    dsimp only [cw]
    omega
  have hadm : RelWord.IsAdmissible E.rel R := by
    exact isAdmissible_relatorWord₂ (by simpa using hbase) hloxfam ms
  obtain ⟨py, hpy0, hpylen, hpy, hpylet, hpyval, hpynorm⟩ :=
    exists_side_spelling₂ E hN hy
  obtain ⟨pz, hpz0, hpzlen, hpz, hpzlet, hpzval, _hpznorm⟩ :=
    exists_side_spelling₂ E hN hz
  have hwadm : RelWord.IsAdmissible E.rel (R.rotate c) :=
    isAdmissible_rotate hadm c
  have hw'adm : RelWord.IsAdmissible E.rel (R.rotate (c + shift)) :=
    isAdmissible_rotate hadm (c + shift)
  have hqlet : ∀ x ∈ u, E.rel.IsLetter x := by
    intro x hx
    refine hwadm x ?_
    rw [hu]
    exact List.mem_append_left _ hx
  have hslet : ∀ x ∈ u', E.rel.IsLetter x := by
    intro x hx
    refine hw'adm x ?_
    rw [hu']
    exact List.mem_append_left _ hx
  have hlet4 : ∀ x ∈ py ++ u ++ pz ++ GGT.OsinComponents.revWord u',
      E.rel.IsLetter x := by
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · rcases List.mem_append.mp hx1 with hx3 | hx4
      · rcases List.mem_append.mp hx3 with hx5 | hx6
        · exact hpylet x hx5
        · exact hqlet x hx6
      · exact hpzlet x hx4
    · exact isAdmissible_revWord hsymm hslet x hx2
  have hclose : GGT.RelLetter.listVal u' = GGT.RelLetter.listVal py *
      GGT.RelLetter.listVal u * GGT.RelLetter.listVal pz := by
    rw [hpyval, hpzval]
    exact hval
  have hcu : ∀ i j : ℕ, i ≤ j → j ≤ u.length →
      j - i ≤ wordDist E.rel.alphabet.carrier
        (GGT.OsinComponents.vertex (1 : G) u i)
        (GGT.OsinComponents.vertex (1 : G) u j) + blockConst [baseLetter] cw := by
    intro i j hij hj
    have hvi : GGT.OsinComponents.vertex (1 : G) u i =
        GGT.OsinComponents.vertex (1 : G) (R.rotate c) i := by
      rw [hu]
      exact (GGT.OsinComponents.vertex_append_of_le u _ 1 i (by omega)).symm
    have hvj : GGT.OsinComponents.vertex (1 : G) u j =
        GGT.OsinComponents.vertex (1 : G) (R.rotate c) j := by
      rw [hu]
      exact (GGT.OsinComponents.vertex_append_of_le u _ 1 j hj).symm
    have hc := hcount (R.rotate c) (RelWord.Sym.rot c RelWord.Sym.base)
      i j hij (by simpa using le_trans hj huLen)
    rw [hvi, hvj]
    dsimp only [cw]
    simp only [blockConst, List.length_singleton] at hc ⊢
    omega
  have hcu' : ∀ i j : ℕ, i ≤ j → j ≤ u'.length →
      j - i ≤ wordDist E.rel.alphabet.carrier
        (GGT.OsinComponents.vertex (1 : G) u' i)
        (GGT.OsinComponents.vertex (1 : G) u' j) + blockConst [baseLetter] cw := by
    intro i j hij hj
    have hvi : GGT.OsinComponents.vertex (1 : G) u' i =
        GGT.OsinComponents.vertex (1 : G) (R.rotate (c + shift)) i := by
      rw [hu']
      exact (GGT.OsinComponents.vertex_append_of_le u' _ 1 i (by omega)).symm
    have hvj : GGT.OsinComponents.vertex (1 : G) u' j =
        GGT.OsinComponents.vertex (1 : G) (R.rotate (c + shift)) j := by
      rw [hu']
      exact (GGT.OsinComponents.vertex_append_of_le u' _ 1 j hj).symm
    have hc := hcount (R.rotate (c + shift))
      (RelWord.Sym.rot (c + shift) RelWord.Sym.base) i j hij
      (by simpa using le_trans hj hu'Len)
    rw [hvi, hvj]
    dsimp only [cw]
    simp only [blockConst, List.length_singleton] at hc ⊢
    omega
  have hqg := fourGonQG_of_sides E.rel (le_trans hpylen hshort)
    (le_trans hpzlen hshort) hcu hcu'
  have hqgq : ∀ i j : ℕ, i ≤ j → j ≤ u.length →
      ((j - i : ℕ) : ℝ) / 1 - ((blockConst [baseLetter] cw : ℕ) : ℝ) ≤
        ((wordDist E.rel.alphabet.carrier
          (GGT.OsinComponents.vertex (1 : G) u i)
          (GGT.OsinComponents.vertex (1 : G) u j) : ℕ) : ℝ) :=
    fun i j hij hj => qgClause_of_le (hcu i j hij hj)
  have hqgs : ∀ i j : ℕ, i ≤ j → j ≤ u'.length →
      ((j - i : ℕ) : ℝ) / 1 - ((blockConst [baseLetter] cw : ℕ) : ℝ) ≤
        ((wordDist E.rel.alphabet.carrier
          (GGT.OsinComponents.vertex (1 : G) u' i)
          (GGT.OsinComponents.vertex (1 : G) u' j) : ℕ) : ℝ) :=
    fun i j hij hj => qgClause_of_le (hcu' i j hij hj)
  have hside := hdesign.sideExclusionAt E heven hcount hW
  obtain ⟨hqside, hsside⟩ := hside py pz u u'
    ⟨R.rotate c, middle ++ u' ++ tail,
      RelWord.Sym.rot c RelWord.Sym.base, hu⟩
    ⟨R.rotate (c + shift), tail ++ u ++ middle,
      RelWord.Sym.rot (c + shift) RelWord.Sym.base, hu'⟩
    hpy hpz hpy0 hpz0
  obtain ⟨d, b, e, k, hd, he, hld, hk0, hk, ⟨x, hx⟩,
      ⟨h, hh, hc⟩, _⟩ :=
    exists_match_with_trivialGap hdisj hdesign.2.1 (injective_pow_lox₂ E)
      hdesign.2.2.2.1 (fun m hm b => hdesign.2.2.1 m hm b b) hCm
      hmsfive hpair hmatch (by simp) hu hu' hlong hpy hpz hpy0 hpz0
      hlet4 hslet hclose hqg hqside hsside
  obtain ⟨f, hf, hef, hlk⟩ := exponent_eq_of_pieceMatch
    hdesign.2.2.2.1 hpair (by simp) hu hu' hpy hpz hpy0 hpz0 hlet4
      hclose hqg hqside hsside he hd hk0 hk hld hx hh hc
  have hinj' : ∀ b : Bool, Function.Injective
      (fun n : ℕ => (if b then E.lox true else E.lox false) ^ n) := by
    intro b
    rw [ite_apply_eq E.lox b]
    exact injective_pow_lox₂ E b
  have huLen' : u.length ≤
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms).length := by
    simpa only [R] using huLen
  have hu'Len' : u'.length ≤
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms).length := by
    simpa only [R] using hu'Len
  have hpos := position_eq_of_alignedMatch
    (p := [baseLetter]) (h₀ := E.lox false) (h₁ := E.lox true)
    hinj' hdesign.2.1 (lt_of_lt_of_le hd huLen')
    (lt_of_lt_of_le (by omega : k - 1 < u'.length) hu'Len')
    hef hld hlk
  have hlen : R.length = u.length + middle.length + u'.length + tail.length := by
    have := congrArg List.length hsplit
    simp only [List.length_rotate, List.length_append] at this
    omega
  have hdR : d < R.length := by rw [hlen]; omega
  have hshiftkR : shift + (k - 1) < R.length := by
    dsimp only [shift]
    rw [hlen]
    omega
  have hmod : d % R.length = (shift + (k - 1)) % R.length := by
    have hm : c + d ≡ c + (shift + (k - 1)) [MOD R.length] := by
      change (c + d) % R.length = (c + (shift + (k - 1))) % R.length
      simpa only [R, Nat.add_assoc] using hpos
    exact Nat.ModEq.add_left_cancel' c hm
  rw [Nat.mod_eq_of_lt hdR, Nat.mod_eq_of_lt hshiftkR] at hmod
  have hpin := GGT.OsinComponents.index_le_of_connector_qg E.rel hqlet hslet
    hqgq hqgs (le_refl _) (le_of_lt hd) hk hpynorm hh hc
  omega

/-- **Both disjoint occurrences in a direct prime match are short.** -/
theorem directPrime_lengths_le_of_exactDesign_rotate
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N)
    {epsD Cm designRho diffRadius W target : ℕ}
    {baseLetter : G} (hbase : baseLetter ∈ E.rel.base) {eps : ℕ}
    {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hCm : Cm * 4 ≤ designRho)
    (hpair : GGT.OsinComponents.MatchedPairOutput E.rel epsD
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hmatch : GGT.OsinComponents.DeepMatchOutput E.rel Cm
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hmsfive : 5 ≤ ms.length)
    {c : ℕ} {u middle u' tail : List (GGT.RelLetter G Bool)}
    (hsplit :
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms).rotate c =
        u ++ middle ++ u' ++ tail)
    {y z : G} (hy : wordNorm E.rel.base y ≤ eps)
    (hz : wordNorm E.rel.base z ≤ eps)
    (hval : GGT.RelLetter.listVal u' = y * GGT.RelLetter.listVal u * z) :
    max u.length u'.length ≤
      eps + 2 + blockConst [baseLetter] (max 1 (eps + 2)) := by
  have hu := directPrimeSource_length_le_of_exactDesign_rotate E hN hbase
    hdesign hcount heven hW hCm hpair hmatch hmsfive hsplit hy hz hval
  let shift := u.length + middle.length
  have hsplit' :
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms).rotate
          (c + shift) = u' ++ tail ++ u ++ middle := by
    rw [← List.rotate_rotate, hsplit]
    exact rotate_four_append_to_third u middle u' tail
  have hyinv : wordNorm E.rel.base y⁻¹ ≤ eps := by
    rw [wordNorm_inv (isSymmetricGeneratingSet_base₂ E) y]
    exact hy
  have hzinv : wordNorm E.rel.base z⁻¹ ≤ eps := by
    rw [wordNorm_inv (isSymmetricGeneratingSet_base₂ E) z]
    exact hz
  have hval' : GGT.RelLetter.listVal u =
      y⁻¹ * GGT.RelLetter.listVal u' * z⁻¹ := by
    rw [hval]
    group
  have hu' := directPrimeSource_length_le_of_exactDesign_rotate E hN hbase
    hdesign hcount heven hW hCm hpair hmatch hmsfive hsplit' hyinv hzinv hval'
  exact max_le hu hu'

/-- **Direct prime matches are uniformly short in every symmetrized member.**

For a rotation of the formal inverse, formally invert the whole cyclic
decomposition and rotate past the old tail.  This turns it into a rotation of
the original relator with the two inverse occurrences in their cyclic order,
so the direct positional theorem applies unchanged. -/
theorem directPrime_lengths_le_of_exactDesign
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N)
    {epsD Cm designRho diffRadius W target : ℕ}
    {baseLetter : G} (hbase : baseLetter ∈ E.rel.base) {eps : ℕ}
    {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hCm : Cm * 4 ≤ designRho)
    (hpair : GGT.OsinComponents.MatchedPairOutput E.rel epsD
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hmatch : GGT.OsinComponents.DeepMatchOutput E.rel Cm
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hmsfive : 5 ≤ ms.length)
    {u middle u' tail v : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v)
    (hsplit : v = u ++ middle ++ u' ++ tail)
    {y z : G} (hy : wordNorm E.rel.base y ≤ eps)
    (hz : wordNorm E.rel.base z ≤ eps)
    (hval : GGT.RelLetter.listVal u' = y * GGT.RelLetter.listVal u * z) :
    max u.length u'.length ≤
      eps + 2 + blockConst [baseLetter] (max 1 (eps + 2)) := by
  let R := relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms
  rcases hv.exists_rotate with ⟨c, hc⟩ | ⟨c, hc⟩
  · have hsplit' : R.rotate c = u ++ middle ++ u' ++ tail := by
      rw [← hc]
      exact hsplit
    exact directPrime_lengths_le_of_exactDesign_rotate E hN hbase hdesign
      hcount heven hW hCm hpair hmatch hmsfive hsplit' hy hz hval
  · have hsplitInv :
        RelWord.revInv v = RelWord.revInv tail ++ RelWord.revInv u' ++
          RelWord.revInv middle ++ RelWord.revInv u := by
      rw [hsplit, RelWord.revInv_append, RelWord.revInv_append,
        RelWord.revInv_append]
      simp only [List.append_assoc]
    obtain ⟨d, hd⟩ := RelWord.exists_revInv_rotate (RelWord.revInv R) c
    have hbaseRot : R.rotate d = RelWord.revInv tail ++ RelWord.revInv u' ++
        RelWord.revInv middle ++ RelWord.revInv u := by
      rw [← hsplitInv, hc, hd, RelWord.revInv_revInv]
    let first := RelWord.revInv tail
    let rest := RelWord.revInv u' ++ RelWord.revInv middle ++ RelWord.revInv u
    have hrot : R.rotate (d + first.length) =
        RelWord.revInv u' ++ RelWord.revInv middle ++
          RelWord.revInv u ++ RelWord.revInv tail := by
      rw [← List.rotate_rotate, hbaseRot]
      have htwo : (first ++ rest).rotate first.length = rest ++ first :=
        rotate_append_to_second first rest
      simpa only [first, rest, List.append_assoc] using htwo
    have hvalInv : GGT.RelLetter.listVal (RelWord.revInv u) =
        z * GGT.RelLetter.listVal (RelWord.revInv u') * y := by
      rw [RelWord.listVal_revInv, RelWord.listVal_revInv, hval]
      group
    have hbound := directPrime_lengths_le_of_exactDesign_rotate E hN hbase
      hdesign hcount heven hW hCm hpair hmatch hmsfive hrot hz hy hvalInv
    simpa only [RelWord.length_revInv, max_comm] using hbound

/-- **A long direct prefix cannot match a prefix of the opposite orientation.** -/
theorem false_of_exactDesign_mixed_long_prefixes_rotate
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N)
    {epsD Cm designRho diffRadius W target : ℕ}
    {baseLetter : G} (hbase : baseLetter ∈ E.rel.base) {eps : ℕ}
    {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hCm : Cm * 4 ≤ designRho)
    (hpair : GGT.OsinComponents.MatchedPairOutput E.rel epsD
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hmatch : GGT.OsinComponents.DeepMatchOutput E.rel Cm
      (blockConst [baseLetter] (max 1 (eps + 2))))
    {c c' : ℕ} {u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms).rotate c =
      u ++ tl)
    (hw' : (RelWord.revInv
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms)).rotate c' =
      u' ++ tl')
    (hlong : [baseLetter].length +
      blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 1 < u.length)
    (hmslong : [baseLetter].length +
      5 * blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 2 < ms.length)
    {y z : G} (hy : wordNorm E.rel.base y ≤ eps)
    (hz : wordNorm E.rel.base z ≤ eps)
    (hval : GGT.RelLetter.listVal u' = y * GGT.RelLetter.listVal u * z) :
    False := by
  let cw := max 1 (eps + 2)
  let R := relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms
  change R.rotate c = u ++ tl at hw
  change (RelWord.revInv R).rotate c' = u' ++ tl' at hw'
  have hsymm : ∀ g ∈ E.rel.base, g⁻¹ ∈ E.rel.base :=
    fun g hg => (isSymmetricGeneratingSet_base₂ E).inv_mem g hg
  have hloxfam : ∀ b : Bool, E.lox b ∈ E.rel.fam b := by
    intro b
    rw [E.fam_eq]
    exact E.lox_mem b
  have hshort : eps + 2 ≤ blockConst [baseLetter] cw := by
    show eps + 2 ≤ [baseLetter].length + cw
    dsimp only [cw]
    omega
  have hadm : RelWord.IsAdmissible E.rel R := by
    exact isAdmissible_relatorWord₂ (by simpa using hbase) hloxfam ms
  obtain ⟨py, hpy0, hpylen, hpy, hpylet, hpyval, hpynorm⟩ :=
    exists_side_spelling₂ E hN hy
  obtain ⟨pz, hpz0, hpzlen, hpz, hpzlet, hpzval, _hpznorm⟩ :=
    exists_side_spelling₂ E hN hz
  have hwadm : RelWord.IsAdmissible E.rel (R.rotate c) :=
    isAdmissible_rotate hadm c
  have hw'adm : RelWord.IsAdmissible E.rel ((RelWord.revInv R).rotate c') :=
    isAdmissible_rotate (isAdmissible_revInv hsymm hadm) c'
  have hqlet : ∀ x ∈ u, E.rel.IsLetter x := by
    intro x hx
    refine hwadm x ?_
    rw [hw]
    exact List.mem_append_left _ hx
  have hslet : ∀ x ∈ u', E.rel.IsLetter x := by
    intro x hx
    refine hw'adm x ?_
    rw [hw']
    exact List.mem_append_left _ hx
  have hlet4 : ∀ x ∈ py ++ u ++ pz ++ GGT.OsinComponents.revWord u',
      E.rel.IsLetter x := by
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · rcases List.mem_append.mp hx1 with hx3 | hx4
      · rcases List.mem_append.mp hx3 with hx5 | hx6
        · exact hpylet x hx5
        · exact hqlet x hx6
      · exact hpzlet x hx4
    · exact isAdmissible_revWord hsymm hslet x hx2
  have hclose : GGT.RelLetter.listVal u' = GGT.RelLetter.listVal py *
      GGT.RelLetter.listVal u * GGT.RelLetter.listVal pz := by
    rw [hpyval, hpzval]
    exact hval
  have hcu : ∀ i j : ℕ, i ≤ j → j ≤ u.length →
      j - i ≤ wordDist E.rel.alphabet.carrier
        (GGT.OsinComponents.vertex (1 : G) u i)
        (GGT.OsinComponents.vertex (1 : G) u j) + blockConst [baseLetter] cw := by
    intro i j hij hj
    have hvi : GGT.OsinComponents.vertex (1 : G) u i =
        GGT.OsinComponents.vertex (1 : G) (R.rotate c) i := by
      rw [hw]
      exact (GGT.OsinComponents.vertex_append_of_le u tl 1 i (by omega)).symm
    have hvj : GGT.OsinComponents.vertex (1 : G) u j =
        GGT.OsinComponents.vertex (1 : G) (R.rotate c) j := by
      rw [hw]
      exact (GGT.OsinComponents.vertex_append_of_le u tl 1 j hj).symm
    have hc := hcount (R.rotate c) (RelWord.Sym.rot c RelWord.Sym.base)
      i j hij (by have h := congrArg List.length hw
                  rw [List.length_rotate, List.length_append] at h
                  simpa using (show j ≤ R.length by omega))
    rw [hvi, hvj]
    dsimp only [cw]
    simp only [blockConst, List.length_singleton] at hc ⊢
    omega
  have hcu' : ∀ i j : ℕ, i ≤ j → j ≤ u'.length →
      j - i ≤ wordDist E.rel.alphabet.carrier
        (GGT.OsinComponents.vertex (1 : G) u' i)
        (GGT.OsinComponents.vertex (1 : G) u' j) + blockConst [baseLetter] cw := by
    intro i j hij hj
    have hvi : GGT.OsinComponents.vertex (1 : G) u' i =
        GGT.OsinComponents.vertex (1 : G) ((RelWord.revInv R).rotate c') i := by
      rw [hw']
      exact (GGT.OsinComponents.vertex_append_of_le u' tl' 1 i (by omega)).symm
    have hvj : GGT.OsinComponents.vertex (1 : G) u' j =
        GGT.OsinComponents.vertex (1 : G) ((RelWord.revInv R).rotate c') j := by
      rw [hw']
      exact (GGT.OsinComponents.vertex_append_of_le u' tl' 1 j hj).symm
    have hc := hcount ((RelWord.revInv R).rotate c')
      (RelWord.Sym.rot c' (RelWord.Sym.inv RelWord.Sym.base)) i j hij
      (by have h := congrArg List.length hw'
          rw [List.length_rotate, RelWord.length_revInv, List.length_append] at h
          have hjR : j ≤ R.length := by omega
          have hjInv : j ≤ (RelWord.revInv R).length := by
            rw [RelWord.length_revInv]
            exact hjR
          simpa using hjInv)
    rw [hvi, hvj]
    dsimp only [cw]
    simp only [blockConst, List.length_singleton] at hc ⊢
    omega
  have hqg := fourGonQG_of_sides E.rel (le_trans hpylen hshort)
    (le_trans hpzlen hshort) hcu hcu'
  have hqgq : ∀ i j : ℕ, i ≤ j → j ≤ u.length →
      ((j - i : ℕ) : ℝ) / 1 - ((blockConst [baseLetter] cw : ℕ) : ℝ) ≤
        ((wordDist E.rel.alphabet.carrier
          (GGT.OsinComponents.vertex (1 : G) u i)
          (GGT.OsinComponents.vertex (1 : G) u j) : ℕ) : ℝ) :=
    fun i j hij hj => qgClause_of_le (hcu i j hij hj)
  have hqgs : ∀ i j : ℕ, i ≤ j → j ≤ u'.length →
      ((j - i : ℕ) : ℝ) / 1 - ((blockConst [baseLetter] cw : ℕ) : ℝ) ≤
        ((wordDist E.rel.alphabet.carrier
          (GGT.OsinComponents.vertex (1 : G) u' i)
          (GGT.OsinComponents.vertex (1 : G) u' j) : ℕ) : ℝ) :=
    fun i j hij hj => qgClause_of_le (hcu' i j hij hj)
  have hside := hdesign.sideExclusionAt E heven hcount hW
  obtain ⟨hqside, hsside⟩ := hside py pz u u'
    ⟨R.rotate c, tl, RelWord.Sym.rot c RelWord.Sym.base, hw⟩
    ⟨(RelWord.revInv R).rotate c', tl',
      RelWord.Sym.rot c' (RelWord.Sym.inv RelWord.Sym.base), hw'⟩
    hpy hpz hpy0 hpz0
  exact false_of_mixedMatch_piece hpair hmatch hdesign.2.1
    (injective_pow_lox₂ E) hdesign.2.2.2.1
    (fun m hm b => hdesign.2.2.1 m hm b b) hCm (by simp) hw hw'
    hlong hmslong hpy hpz hpy0 hpz0 hlet4 hclose hqg hqlet hslet
    hqgq hqgs (le_refl _) hpynorm hqside hsside

/-- **The first occurrence in an inverse prime match is uniformly short.** -/
theorem inversePrimeSource_length_le_of_exactDesign
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N)
    {epsD Cm designRho diffRadius W target : ℕ}
    {baseLetter : G} (hbase : baseLetter ∈ E.rel.base) {eps : ℕ}
    {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hCm : Cm * 4 ≤ designRho)
    (hpair : GGT.OsinComponents.MatchedPairOutput E.rel epsD
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hmatch : GGT.OsinComponents.DeepMatchOutput E.rel Cm
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hmslong : [baseLetter].length +
      5 * blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 2 < ms.length)
    {u middle u' tail v : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v)
    (hsplit : v = u ++ middle ++ u' ++ tail)
    {y z : G} (hy : wordNorm E.rel.base y ≤ eps)
    (hz : wordNorm E.rel.base z ≤ eps)
    (hval : GGT.RelLetter.listVal u' =
      y * (GGT.RelLetter.listVal u)⁻¹ * z) :
    u.length ≤ [baseLetter].length +
      blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 1 := by
  by_contra hnot
  have hlong : [baseLetter].length +
      blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 1 < u.length := by
    omega
  let R := relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms
  have hrevSplit : RelWord.revInv v = RelWord.revInv tail ++
      RelWord.revInv u' ++ RelWord.revInv middle ++ RelWord.revInv u := by
    rw [hsplit, RelWord.revInv_append, RelWord.revInv_append,
      RelWord.revInv_append]
    simp only [List.append_assoc]
  rcases hv.exists_rotate with ⟨c, hc⟩ | ⟨c, hc⟩
  · have hfirst : R.rotate c = u ++ (middle ++ u' ++ tail) := by
      rw [← hc]
      simpa only [List.append_assoc] using hsplit
    obtain ⟨d, hd⟩ := RelWord.exists_revInv_rotate R c
    have hrevOrient : (RelWord.revInv R).rotate d = RelWord.revInv v := by
      rw [hc]
      exact hd.symm
    let first := RelWord.revInv tail
    let rest := RelWord.revInv u' ++ RelWord.revInv middle ++ RelWord.revInv u
    have hsecond : (RelWord.revInv R).rotate (d + first.length) =
        RelWord.revInv u' ++
          (RelWord.revInv middle ++ RelWord.revInv u ++ RelWord.revInv tail) := by
      rw [← List.rotate_rotate, hrevOrient, hrevSplit]
      have ht := rotate_append_to_second first rest
      simpa only [first, rest, List.append_assoc] using ht
    have hzinv : wordNorm E.rel.base z⁻¹ ≤ eps := by
      rw [wordNorm_inv (isSymmetricGeneratingSet_base₂ E) z]
      exact hz
    have hyinv : wordNorm E.rel.base y⁻¹ ≤ eps := by
      rw [wordNorm_inv (isSymmetricGeneratingSet_base₂ E) y]
      exact hy
    have hvalInv : GGT.RelLetter.listVal (RelWord.revInv u') =
        z⁻¹ * GGT.RelLetter.listVal u * y⁻¹ := by
      rw [RelWord.listVal_revInv, hval]
      group
    exact false_of_exactDesign_mixed_long_prefixes_rotate E hN hbase hdesign
      hcount heven hW hCm hpair hmatch hfirst hsecond hlong hmslong
      hzinv hyinv hvalInv
  · let shift := u.length + middle.length
    have hsecond : (RelWord.revInv R).rotate (c + shift) =
        u' ++ (tail ++ u ++ middle) := by
      rw [← List.rotate_rotate, ← hc, hsplit]
      simpa only [shift, List.append_assoc] using
        rotate_four_append_to_third u middle u' tail
    obtain ⟨d, hd⟩ := RelWord.exists_revInv_rotate (RelWord.revInv R) c
    have hrevOrient : R.rotate d = RelWord.revInv v := by
      rw [hc, hd, RelWord.revInv_revInv]
    let first := RelWord.revInv tail ++ RelWord.revInv u' ++ RelWord.revInv middle
    let rest := RelWord.revInv u
    have hfirst : R.rotate (d + first.length) =
        RelWord.revInv u ++
          (RelWord.revInv tail ++ RelWord.revInv u' ++ RelWord.revInv middle) := by
      rw [← List.rotate_rotate, hrevOrient, hrevSplit]
      have ht := rotate_append_to_second first rest
      simpa only [first, rest, List.append_assoc] using ht
    have hval' : GGT.RelLetter.listVal u' =
        y * GGT.RelLetter.listVal (RelWord.revInv u) * z := by
      rw [RelWord.listVal_revInv]
      exact hval
    have hlong' : [baseLetter].length +
        blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 1 <
          (RelWord.revInv u).length := by
      rw [RelWord.length_revInv]
      exact hlong
    exact false_of_exactDesign_mixed_long_prefixes_rotate E hN hbase hdesign
      hcount heven hW hCm hpair hmatch hfirst hsecond hlong' hmslong hy hz hval'

/-- **Both occurrences in an inverse prime match are uniformly short.** -/
theorem inversePrime_lengths_le_of_exactDesign
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N)
    {epsD Cm designRho diffRadius W target : ℕ}
    {baseLetter : G} (hbase : baseLetter ∈ E.rel.base) {eps : ℕ}
    {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hCm : Cm * 4 ≤ designRho)
    (hpair : GGT.OsinComponents.MatchedPairOutput E.rel epsD
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hmatch : GGT.OsinComponents.DeepMatchOutput E.rel Cm
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hmslong : [baseLetter].length +
      5 * blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 2 < ms.length)
    {u middle u' tail v : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v)
    (hsplit : v = u ++ middle ++ u' ++ tail)
    {y z : G} (hy : wordNorm E.rel.base y ≤ eps)
    (hz : wordNorm E.rel.base z ≤ eps)
    (hval : GGT.RelLetter.listVal u' =
      y * (GGT.RelLetter.listVal u)⁻¹ * z) :
    max u.length u'.length ≤ [baseLetter].length +
      blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 1 := by
  have hu := inversePrimeSource_length_le_of_exactDesign E hN hbase hdesign
    hcount heven hW hCm hpair hmatch hmslong hv hsplit hy hz hval
  let shift := u.length + middle.length
  have hsplit' : v.rotate shift = u' ++ tail ++ u ++ middle := by
    rw [hsplit]
    exact rotate_four_append_to_third u middle u' tail
  have hval' : GGT.RelLetter.listVal u =
      z * (GGT.RelLetter.listVal u')⁻¹ * y := by
    rw [hval]
    group
  have hu' := inversePrimeSource_length_le_of_exactDesign E hN hbase hdesign
    hcount heven hW hCm hpair hmatch hmslong
      (RelWord.Sym.rot shift hv) hsplit' hz hy hval'
  exact max_le hu hu'

/-- **Every published primepiece of the exact relator is uniformly short.** -/
theorem primePiece_lengths_le_of_exactDesign
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N)
    {epsD Cm designRho diffRadius W target : ℕ}
    {baseLetter : G} (hbase : baseLetter ∈ E.rel.base) {eps : ℕ}
    {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hCm : Cm * 4 ≤ designRho)
    (hpair : GGT.OsinComponents.MatchedPairOutput E.rel epsD
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hmatch : GGT.OsinComponents.DeepMatchOutput E.rel Cm
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hmslong : [baseLetter].length +
      5 * blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 2 < ms.length)
    {u u' v : List (GGT.RelLetter G Bool)}
    (hp : RelWord.IsPrimePiece E.rel
      (RelWord.symmetrized
        (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms))
      eps u u' v) :
    max u.length u'.length ≤ [baseLetter].length +
      blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 1 := by
  rcases hp with ⟨hv, middle, tail, hsplit, y, z, hy, hz, hval | hval⟩
  · have hfive : 5 ≤ ms.length := by
      simp only [blockSeparation, blockConst, List.length_singleton] at hmslong
      omega
    have hdirect := directPrime_lengths_le_of_exactDesign E hN hbase hdesign
      hcount heven hW hCm hpair hmatch hfive (RelWord.mem_symmetrized.mp hv)
      hsplit hy hz hval
    simp only [blockConst, blockSeparation, List.length_singleton] at hdirect ⊢
    omega
  · exact inversePrime_lengths_le_of_exactDesign E hN hbase hdesign
      hcount heven hW hCm hpair hmatch hmslong (RelWord.mem_symmetrized.mp hv)
      hsplit hy hz hval

/-- **The long-prefix conclusion at one exact relator design.**

This is the geometric body of the separation producer, with the chosen list
and its exact avoidance certificates exposed and with no `w' ≠ w` premise.
That omission is essential for Hull's same-word published pieces. -/
theorem listVal_conj_of_exactDesign_long_prefixes
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N)
    {epsD Cm designRho diffRadius W target : ℕ}
    {baseLetter : G} (hbase : baseLetter ∈ E.rel.base) {eps : ℕ}
    {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hCm : Cm * 4 ≤ designRho)
    (hpair : GGT.OsinComponents.MatchedPairOutput E.rel epsD
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hmatch : GGT.OsinComponents.DeepMatchOutput E.rel Cm
      (blockConst [baseLetter] (max 1 (eps + 2))))
    {w w' u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) w)
    (hw' : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) w')
    (hu : w = u ++ tl) (hu' : w' = u' ++ tl')
    (hlong : [baseLetter].length +
      blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 1 < u.length)
    (hmslong : [baseLetter].length +
      5 * blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 2 < ms.length)
    {y z : G} (hy : wordNorm E.rel.base y ≤ eps)
    (hz : wordNorm E.rel.base z ≤ eps)
    (hval : GGT.RelLetter.listVal u' = y * GGT.RelLetter.listVal u * z) :
    GGT.RelLetter.listVal w' =
      y * GGT.RelLetter.listVal w * y⁻¹ := by
  let cw := max 1 (eps + 2)
  have hsymm : ∀ g ∈ E.rel.base, g⁻¹ ∈ E.rel.base :=
    fun g hg => (isSymmetricGeneratingSet_base₂ E).inv_mem g hg
  have hloxfam : ∀ b : Bool, E.lox b ∈ E.rel.fam b := by
    intro b
    rw [E.fam_eq]
    exact E.lox_mem b
  have hdisj : ∀ x : G, x ∈ E.rel.fam false → x ∈ E.rel.fam true → x = 1 := by
    rw [E.fam_eq]
    exact E.disjoint
  have hmono : blockConst [baseLetter] 1 ≤ blockConst [baseLetter] cw := by
    show [baseLetter].length + 1 ≤ [baseLetter].length + cw
    dsimp only [cw]
    omega
  have hshort : eps + 2 ≤ blockConst [baseLetter] cw := by
    show eps + 2 ≤ [baseLetter].length + cw
    dsimp only [cw]
    omega
  have hadm : RelWord.IsAdmissible E.rel
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) :=
    isAdmissible_relatorWord₂ (by simpa using hbase) hloxfam ms
  obtain ⟨py, hpy0, hpylen, hpy, hpylet, hpyval, hpynorm⟩ :=
    exists_side_spelling₂ E hN hy
  obtain ⟨pz, hpz0, hpzlen, hpz, hpzlet, hpzval, _hpznorm⟩ :=
    exists_side_spelling₂ E hN hz
  have hwadm : RelWord.IsAdmissible E.rel w := isAdmissible_sym hsymm hw hadm
  have hw'adm : RelWord.IsAdmissible E.rel w' := isAdmissible_sym hsymm hw' hadm
  have hqlet : ∀ x ∈ u, E.rel.IsLetter x := by
    intro x hx
    refine hwadm x ?_
    rw [hu]
    exact List.mem_append_left _ hx
  have hslet : ∀ x ∈ u', E.rel.IsLetter x := by
    intro x hx
    refine hw'adm x ?_
    rw [hu']
    exact List.mem_append_left _ hx
  have hlet4 : ∀ x ∈ py ++ u ++ pz ++ GGT.OsinComponents.revWord u',
      E.rel.IsLetter x := by
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · rcases List.mem_append.mp hx1 with hx3 | hx4
      · rcases List.mem_append.mp hx3 with hx5 | hx6
        · exact hpylet x hx5
        · exact hqlet x hx6
      · exact hpzlet x hx4
    · exact isAdmissible_revWord hsymm hslet x hx2
  have hclose : GGT.RelLetter.listVal u' = GGT.RelLetter.listVal py *
      GGT.RelLetter.listVal u * GGT.RelLetter.listVal pz := by
    rw [hpyval, hpzval]
    exact hval
  have hcu : ∀ i j : ℕ, i ≤ j → j ≤ u.length →
      j - i ≤ wordDist E.rel.alphabet.carrier
        (GGT.OsinComponents.vertex (1 : G) u i)
        (GGT.OsinComponents.vertex (1 : G) u j) +
          blockConst [baseLetter] cw := by
    intro i j hij hj
    have hvi : GGT.OsinComponents.vertex (1 : G) u i =
        GGT.OsinComponents.vertex (1 : G) w i := by
      rw [hu]
      exact (GGT.OsinComponents.vertex_append_of_le u tl 1 i (by omega)).symm
    have hvj : GGT.OsinComponents.vertex (1 : G) u j =
        GGT.OsinComponents.vertex (1 : G) w j := by
      rw [hu]
      exact (GGT.OsinComponents.vertex_append_of_le u tl 1 j hj).symm
    have hwlen : j ≤ w.length := by rw [hu, List.length_append]; omega
    have hc := hcount w hw i j hij hwlen
    rw [hvi, hvj]
    omega
  have hcu' : ∀ i j : ℕ, i ≤ j → j ≤ u'.length →
      j - i ≤ wordDist E.rel.alphabet.carrier
        (GGT.OsinComponents.vertex (1 : G) u' i)
        (GGT.OsinComponents.vertex (1 : G) u' j) +
          blockConst [baseLetter] cw := by
    intro i j hij hj
    have hvi : GGT.OsinComponents.vertex (1 : G) u' i =
        GGT.OsinComponents.vertex (1 : G) w' i := by
      rw [hu']
      exact (GGT.OsinComponents.vertex_append_of_le u' tl' 1 i (by omega)).symm
    have hvj : GGT.OsinComponents.vertex (1 : G) u' j =
        GGT.OsinComponents.vertex (1 : G) w' j := by
      rw [hu']
      exact (GGT.OsinComponents.vertex_append_of_le u' tl' 1 j hj).symm
    have hwlen : j ≤ w'.length := by rw [hu', List.length_append]; omega
    have hc := hcount w' hw' i j hij hwlen
    rw [hvi, hvj]
    omega
  have hqg := fourGonQG_of_sides E.rel (le_trans hpylen hshort)
    (le_trans hpzlen hshort) hcu hcu'
  have hqgq : ∀ i j : ℕ, i ≤ j → j ≤ u.length →
      ((j - i : ℕ) : ℝ) / 1 - ((blockConst [baseLetter] cw : ℕ) : ℝ) ≤
        ((wordDist E.rel.alphabet.carrier
          (GGT.OsinComponents.vertex (1 : G) u i)
          (GGT.OsinComponents.vertex (1 : G) u j) : ℕ) : ℝ) :=
    fun i j hij hj => qgClause_of_le (hcu i j hij hj)
  have hqgs : ∀ i j : ℕ, i ≤ j → j ≤ u'.length →
      ((j - i : ℕ) : ℝ) / 1 - ((blockConst [baseLetter] cw : ℕ) : ℝ) ≤
        ((wordDist E.rel.alphabet.carrier
          (GGT.OsinComponents.vertex (1 : G) u' i)
          (GGT.OsinComponents.vertex (1 : G) u' j) : ℕ) : ℝ) :=
    fun i j hij hj => qgClause_of_le (hcu' i j hij hj)
  have hside := hdesign.sideExclusionAt E heven hcount hW
  obtain ⟨hqside, hsside⟩ :=
    hside py pz u u' ⟨w, tl, hw, hu⟩ ⟨w', tl', hw', hu'⟩
      hpy hpz hpy0 hpz0
  have hconj := listVal_conj_of_sym_pieces hpair hmatch hdesign.2.1
    (injective_pow_lox₂ E) hsymm hdesign.2.2.2.1 hdisj
    (fun m hm b => hdesign.2.2.1 m hm b b) hCm (by simp)
    hw hw' hu hu' hlong hmslong hpy hpz hpy0 hpz0 hlet4 hclose hqg
    hqlet hslet hqgq hqgs (le_refl _) hpynorm hqside hsside
  rw [hpyval] at hconj
  exact hconj

/-- **A same-word published piece of the exact relator is uniformly short.**

If its first exposed prefix crossed the fixed long-prefix threshold, the exact
quadrilateral theorem would give the full-word conjugacy forbidden in the
definition.  Reversing the short connector equation gives the same bound for
the second prefix. -/
theorem sameWordPublishedPiece_lengths_le_of_exactDesign
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N)
    {epsD Cm designRho diffRadius W target : ℕ}
    {baseLetter : G} (hbase : baseLetter ∈ E.rel.base) {eps : ℕ}
    {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hCm : Cm * 4 ≤ designRho)
    (hpair : GGT.OsinComponents.MatchedPairOutput E.rel epsD
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hmatch : GGT.OsinComponents.DeepMatchOutput E.rel Cm
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hmslong : [baseLetter].length +
      5 * blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 2 < ms.length)
    {u u' v : List (GGT.RelLetter G Bool)}
    (hp : RelWord.IsSameWordPublishedPiece E.rel
      (RelWord.symmetrized
        (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms))
      eps u u' v) :
    max u.length u'.length ≤
      [baseLetter].length + blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 1 := by
  rcases hp with ⟨hv, ⟨tl, hu⟩, ⟨tl', hu'⟩,
    y, z, hy, hz, hval, hexcl⟩
  have hvSym := RelWord.mem_symmetrized.mp hv
  have hlu : u.length ≤
      [baseLetter].length + blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 1 := by
    by_contra hnot
    have hlong : [baseLetter].length +
        blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 1 < u.length := by
      omega
    exact hexcl (listVal_conj_of_exactDesign_long_prefixes E hN hbase
      hdesign hcount heven hW hCm hpair hmatch hvSym hvSym hu hu' hlong
      hmslong hy hz hval)
  have hlu' : u'.length ≤
      [baseLetter].length + blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 1 := by
    by_contra hnot
    have hlong : [baseLetter].length +
        blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 1 < u'.length := by
      omega
    have hyinv : wordNorm E.rel.base y⁻¹ ≤ eps := by
      rw [wordNorm_inv (isSymmetricGeneratingSet_base₂ E) y]
      exact hy
    have hzinv : wordNorm E.rel.base z⁻¹ ≤ eps := by
      rw [wordNorm_inv (isSymmetricGeneratingSet_base₂ E) z]
      exact hz
    have hval' : GGT.RelLetter.listVal u =
        y⁻¹ * GGT.RelLetter.listVal u' * z⁻¹ := by
      rw [hval]
      group
    have hconj := listVal_conj_of_exactDesign_long_prefixes E hN hbase
      hdesign hcount heven hW hCm hpair hmatch hvSym hvSym hu' hu hlong
      hmslong hyinv hzinv hval'
    have hconj' : GGT.RelLetter.listVal v =
        y⁻¹ * GGT.RelLetter.listVal v * y := by simpa using hconj
    have hcomm : y * GGT.RelLetter.listVal v = GGT.RelLetter.listVal v * y := by
      calc
        y * GGT.RelLetter.listVal v =
            y * (y⁻¹ * GGT.RelLetter.listVal v * y) := congrArg (y * ·) hconj'
        _ = GGT.RelLetter.listVal v * y := by group
    apply hexcl
    rw [hcomm]
    group
  omega

end FixedDesign

end HullSC
end GroupApproximation
