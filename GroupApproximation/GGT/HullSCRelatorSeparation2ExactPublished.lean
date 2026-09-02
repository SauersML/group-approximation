import GroupApproximation.GGT.HullSCRelatorSeparation2RelativeClose
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyFourWay
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyQG
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyShortSide
import GroupApproximation.GGT.HullSCRelatorAdmissible
import GroupApproximation.GGT.HullSCRelatorSeparation2ExactCount
import GroupApproximation.GGT.HullSCPublishedSmallCancellation
import GroupApproximation.GGT.CayleyFourPointConverse

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
    {epsD gapC designRho diffRadius W target : ℕ}
    {baseLetter : G} (hbase : baseLetter ∈ E.rel.base) {eps : ℕ}
    {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hgap : ExactPublishedGapOutput E gapC
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hgapRho : gapC * 4 ≤ designRho) (hgapEps : gapC * 4 ≤ epsD)
    {c : ℕ} {u middle u' tail : List (GGT.RelLetter G Bool)}
    (hsplit :
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms).rotate c =
        u ++ middle ++ u' ++ tail)
    {y z : G} (hy : wordNorm E.rel.alphabet.carrier y ≤ eps)
    (hz : wordNorm E.rel.alphabet.carrier z ≤ eps)
    (hval : GGT.RelLetter.listVal u' = y * GGT.RelLetter.listVal u * z) :
    u.length ≤ eps + 6 + blockConst [baseLetter] (max 1 (eps + 2)) := by
  let cw := max 1 (eps + 2)
  by_cases hshortu : u.length ≤
      eps + 6 + blockConst [baseLetter] (max 1 (eps + 2))
  · exact hshortu
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
  obtain ⟨py, hpy0, hpylen, hpylet, hpyval, hpynorm⟩ :=
    exists_side_spelling₂ E hN hy
  obtain ⟨pz, hpz0, hpzlen, hpzlet, hpzval, _hpznorm⟩ :=
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
  have hlenGap : py.length + pz.length + 2 + 3 ≤
      u.length := by
    have hpyle := hpylen
    have hpzle := hpzlen
    simp only [blockConst, List.length_singleton] at hshortu
    omega
  obtain ⟨b, d, k, hd0, hdend, hcompd, hk1, hk, hcompk, _hstart,
      ⟨h, hh, hc⟩, hxb, hx'b⟩ :=
    hgap hdesign hcount heven hW
      (RelWord.Sym.rot c RelWord.Sym.base) hu
      (RelWord.Sym.rot (c + shift) RelWord.Sym.base) hu'
      py pz hclose hpz0 hlet4 hqg hgapRho hgapEps hlenGap
  have hsourceOf := hcompd.2.2.1 d le_rfl (by omega) (by omega)
  obtain ⟨vq, hlu⟩ := getElem?_comp_of_isCompOf (by omega) hsourceOf
  have hldRaw : (R.rotate c)[d]? = some (GGT.RelLetter.comp b vq) := by
    rw [hu, List.getElem?_append_left (by omega : d < u.length)]
    exact hlu
  obtain ⟨e, he, hvq⟩ := exponent_of_comp_rotate hldRaw
  have hld : (R.rotate c)[d]? = some (GGT.RelLetter.comp b
      ((if b then E.lox true else E.lox false) ^ e)) := by rw [hldRaw, hvq]
  have htargetOf := hcompk.2.2.1 (k - 1) le_rfl (by omega) (by omega)
  obtain ⟨vs, hx⟩ := getElem?_comp_of_isCompOf (by omega) htargetOf
  have hlkRaw : (R.rotate (c + shift))[k - 1]? =
      some (GGT.RelLetter.comp b vs) := by
    rw [hu', List.getElem?_append_left (by omega : k - 1 < u'.length)]
    exact hx
  obtain ⟨f, hf, hvs⟩ := exponent_of_comp_rotate hlkRaw
  have hlk : (R.rotate (c + shift))[k - 1]? = some (GGT.RelLetter.comp b
      ((if b then E.lox true else E.lox false) ^ f)) := by rw [hlkRaw, hvs]
  have hrel := conj_of_matchedPair_letters (py := py) hlu hx
  rw [hvq, hvs, ite_apply_eq E.lox b] at hrel
  have hrel' :
      (GGT.OsinComponents.vertex (1 : G) u' (k - 1))⁻¹ *
            (GGT.RelLetter.listVal py * GGT.OsinComponents.vertex (1 : G) u d) *
          E.lox b ^ e *
        ((GGT.RelLetter.listVal py *
            GGT.OsinComponents.vertex (1 : G) u (d + 1))⁻¹ *
          GGT.OsinComponents.vertex (1 : G) u' k) = E.lox b ^ f := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hrel
  have hef := exponent_eq_of_blockMatch_ball hdesign.2.2.2.1 he hf hxb hx'b hrel'
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
    (i := d) (j := k - 1) hinj' hdesign.2.1 (by omega)
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
  have hpin := GGT.OsinComponents.index_le_of_connector_qg E.rel
    (i := d) (j := k) hqlet hslet hqgq hqgs (le_refl _)
    (by omega) hk hpynorm hh hc
  omega

/-- **Both disjoint occurrences in a direct prime match are short.** -/
theorem directPrime_lengths_le_of_exactDesign_rotate
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N)
    {epsD gapC designRho diffRadius W target : ℕ}
    {baseLetter : G} (hbase : baseLetter ∈ E.rel.base) {eps : ℕ}
    {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hgap : ExactPublishedGapOutput E gapC
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hgapRho : gapC * 4 ≤ designRho) (hgapEps : gapC * 4 ≤ epsD)
    {c : ℕ} {u middle u' tail : List (GGT.RelLetter G Bool)}
    (hsplit :
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms).rotate c =
        u ++ middle ++ u' ++ tail)
    {y z : G} (hy : wordNorm E.rel.alphabet.carrier y ≤ eps)
    (hz : wordNorm E.rel.alphabet.carrier z ≤ eps)
    (hval : GGT.RelLetter.listVal u' = y * GGT.RelLetter.listVal u * z) :
    max u.length u'.length ≤
      eps + 6 + blockConst [baseLetter] (max 1 (eps + 2)) := by
  have hu := directPrimeSource_length_le_of_exactDesign_rotate E hN hbase
    hdesign hcount heven hW hgap hgapRho hgapEps hsplit hy hz hval
  let shift := u.length + middle.length
  have hsplit' :
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms).rotate
          (c + shift) = u' ++ tail ++ u ++ middle := by
    rw [← List.rotate_rotate, hsplit]
    exact rotate_four_append_to_third u middle u' tail
  have hyinv : wordNorm E.rel.alphabet.carrier y⁻¹ ≤ eps := by
    rw [wordNorm_inv E.rel.alphabet.symmetricGenerating y]
    exact hy
  have hzinv : wordNorm E.rel.alphabet.carrier z⁻¹ ≤ eps := by
    rw [wordNorm_inv E.rel.alphabet.symmetricGenerating z]
    exact hz
  have hval' : GGT.RelLetter.listVal u =
      y⁻¹ * GGT.RelLetter.listVal u' * z⁻¹ := by
    rw [hval]
    group
  have hu' := directPrimeSource_length_le_of_exactDesign_rotate E hN hbase
    hdesign hcount heven hW hgap hgapRho hgapEps hsplit' hyinv hzinv hval'
  exact max_le hu hu'

/-- **Direct prime matches are uniformly short in every symmetrized member.**

For a rotation of the formal inverse, formally invert the whole cyclic
decomposition and rotate past the old tail.  This turns it into a rotation of
the original relator with the two inverse occurrences in their cyclic order,
so the direct positional theorem applies unchanged. -/
theorem directPrime_lengths_le_of_exactDesign
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N)
    {epsD gapC designRho diffRadius W target : ℕ}
    {baseLetter : G} (hbase : baseLetter ∈ E.rel.base) {eps : ℕ}
    {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hgap : ExactPublishedGapOutput E gapC
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hgapRho : gapC * 4 ≤ designRho) (hgapEps : gapC * 4 ≤ epsD)
    {u middle u' tail v : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v)
    (hsplit : v = u ++ middle ++ u' ++ tail)
    {y z : G} (hy : wordNorm E.rel.alphabet.carrier y ≤ eps)
    (hz : wordNorm E.rel.alphabet.carrier z ≤ eps)
    (hval : GGT.RelLetter.listVal u' = y * GGT.RelLetter.listVal u * z) :
    max u.length u'.length ≤
      eps + 6 + blockConst [baseLetter] (max 1 (eps + 2)) := by
  let R := relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms
  rcases hv.exists_rotate with ⟨c, hc⟩ | ⟨c, hc⟩
  · have hsplit' : R.rotate c = u ++ middle ++ u' ++ tail := by
      rw [← hc]
      exact hsplit
    exact directPrime_lengths_le_of_exactDesign_rotate E hN hbase hdesign
      hcount heven hW hgap hgapRho hgapEps hsplit' hy hz hval
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
      hdesign hcount heven hW hgap hgapRho hgapEps hrot hz hy hvalInv
    simpa only [RelWord.length_revInv, max_comm] using hbound

/-- **A long direct prefix cannot match a prefix of the opposite orientation.** -/
theorem false_of_exactDesign_mixed_long_prefixes_rotate
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N)
    {epsD adjacentC designRho diffRadius W target : ℕ}
    {baseLetter : G} (hbase : baseLetter ∈ E.rel.base) {eps : ℕ}
    {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hadj : ExactPublishedAdjacentGapOutput E adjacentC
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hadjRho : adjacentC * 4 ≤ designRho)
    (hadjEps : adjacentC * 4 ≤ epsD)
    (hepsRho : epsD ≤ designRho)
    {c c' : ℕ} {u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms).rotate c =
      u ++ tl)
    (hw' : (RelWord.revInv
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms)).rotate c' =
      u' ++ tl')
    (hlong : [baseLetter].length +
      blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 6 < u.length)
    {y z : G} (hy : wordNorm E.rel.alphabet.carrier y ≤ eps)
    (hz : wordNorm E.rel.alphabet.carrier z ≤ eps)
    (hval : GGT.RelLetter.listVal u' = y * GGT.RelLetter.listVal u * z) :
    False := by
  let cw := max 1 (eps + 2)
  let R := relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms
  change R.rotate c = u ++ tl at hw
  change (RelWord.revInv R).rotate c' = u' ++ tl' at hw'
  have hsymm : ∀ g ∈ E.rel.base, g⁻¹ ∈ E.rel.base :=
    fun g hg => (isSymmetricGeneratingSet_base₂ E).inv_mem g hg
  have hdisj : ∀ x : G, x ∈ E.rel.fam false →
      x ∈ E.rel.fam true → x = 1 := by
    rw [E.fam_eq]
    exact E.disjoint
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
  obtain ⟨py, _hpy0, hpylen, hpylet, hpyval, _hpynorm⟩ :=
    exists_side_spelling₂ E hN hy
  obtain ⟨pz, hpz0, hpzlen, hpzlet, hpzval, _hpznorm⟩ :=
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
  have hcapacity : 2 * (py.length + pz.length + 3) + 2 ≤ u.length := by
    have hbaseCapacity := exactPublishedAdjacentCapacity_singleton baseLetter eps
    omega
  obtain ⟨b, b', i, j, j', hi0, hi2, hcomp, hcomp', hj1, hj,
      hcompS, hj'1, hj', hcompS', ⟨h, hh, hconn⟩, ⟨h', hh', hconn'⟩,
      hx, hx', hy', hy''⟩ :=
    hadj hdesign hcount heven hW
      (RelWord.Sym.rot c RelWord.Sym.base) hw
      (RelWord.Sym.rot c' (RelWord.Sym.inv RelWord.Sym.base)) hw'
      py pz hclose hpz0 hlet4 hqg hadjRho hadjEps hcapacity
  exact false_of_relativeAdjacent_direct_revInv hdesign.2.1
    (injective_pow_lox₂ E) hdesign.2.2.2.1
    (fun m hm b => hdesign.2.2.1 m hm b b) hepsRho hdisj (by simp)
    hw hw' hi0 hi2 hcomp hcomp' hj1 hj hcompS hj'1 hj' hcompS'
    hh hh' hconn hconn' hx hx' hy' hy'' hqlet

/-- **The first occurrence in an inverse prime match is uniformly short.** -/
theorem inversePrimeSource_length_le_of_exactDesign
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N)
    {epsD adjacentC designRho diffRadius W target : ℕ}
    {baseLetter : G} (hbase : baseLetter ∈ E.rel.base) {eps : ℕ}
    {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hadj : ExactPublishedAdjacentGapOutput E adjacentC
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hadjRho : adjacentC * 4 ≤ designRho)
    (hadjEps : adjacentC * 4 ≤ epsD)
    (hepsRho : epsD ≤ designRho)
    {u middle u' tail v : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v)
    (hsplit : v = u ++ middle ++ u' ++ tail)
    {y z : G} (hy : wordNorm E.rel.alphabet.carrier y ≤ eps)
    (hz : wordNorm E.rel.alphabet.carrier z ≤ eps)
    (hval : GGT.RelLetter.listVal u' =
      y * (GGT.RelLetter.listVal u)⁻¹ * z) :
    u.length ≤ [baseLetter].length +
      blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 6 := by
  by_contra hnot
  have hlong : [baseLetter].length +
      blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 6 < u.length := by
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
    have hzinv : wordNorm E.rel.alphabet.carrier z⁻¹ ≤ eps := by
      rw [wordNorm_inv E.rel.alphabet.symmetricGenerating z]
      exact hz
    have hyinv : wordNorm E.rel.alphabet.carrier y⁻¹ ≤ eps := by
      rw [wordNorm_inv E.rel.alphabet.symmetricGenerating y]
      exact hy
    have hvalInv : GGT.RelLetter.listVal (RelWord.revInv u') =
        z⁻¹ * GGT.RelLetter.listVal u * y⁻¹ := by
      rw [RelWord.listVal_revInv, hval]
      group
    exact false_of_exactDesign_mixed_long_prefixes_rotate E hN hbase hdesign
      hcount heven hW hadj hadjRho hadjEps hepsRho hfirst hsecond hlong
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
        blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 6 <
          (RelWord.revInv u).length := by
      rw [RelWord.length_revInv]
      exact hlong
    exact false_of_exactDesign_mixed_long_prefixes_rotate E hN hbase hdesign
      hcount heven hW hadj hadjRho hadjEps hepsRho hfirst hsecond hlong'
      hy hz hval'

/-- **Both occurrences in an inverse prime match are uniformly short.** -/
theorem inversePrime_lengths_le_of_exactDesign
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N)
    {epsD adjacentC designRho diffRadius W target : ℕ}
    {baseLetter : G} (hbase : baseLetter ∈ E.rel.base) {eps : ℕ}
    {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hadj : ExactPublishedAdjacentGapOutput E adjacentC
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hadjRho : adjacentC * 4 ≤ designRho)
    (hadjEps : adjacentC * 4 ≤ epsD)
    (hepsRho : epsD ≤ designRho)
    {u middle u' tail v : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v)
    (hsplit : v = u ++ middle ++ u' ++ tail)
    {y z : G} (hy : wordNorm E.rel.alphabet.carrier y ≤ eps)
    (hz : wordNorm E.rel.alphabet.carrier z ≤ eps)
    (hval : GGT.RelLetter.listVal u' =
      y * (GGT.RelLetter.listVal u)⁻¹ * z) :
    max u.length u'.length ≤ [baseLetter].length +
      blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 6 := by
  have hu := inversePrimeSource_length_le_of_exactDesign E hN hbase hdesign
    hcount heven hW hadj hadjRho hadjEps hepsRho hv hsplit hy hz hval
  let shift := u.length + middle.length
  have hsplit' : v.rotate shift = u' ++ tail ++ u ++ middle := by
    rw [hsplit]
    exact rotate_four_append_to_third u middle u' tail
  have hval' : GGT.RelLetter.listVal u =
      z * (GGT.RelLetter.listVal u')⁻¹ * y := by
    rw [hval]
    group
  have hu' := inversePrimeSource_length_le_of_exactDesign E hN hbase hdesign
    hcount heven hW hadj hadjRho hadjEps hepsRho
      (RelWord.Sym.rot shift hv) hsplit' hz hy hval'
  exact max_le hu hu'

/-- **Every published primepiece of the exact relator is uniformly short.** -/
theorem primePiece_lengths_le_of_exactDesign
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N)
    {epsD adjacentC gapC designRho diffRadius W target : ℕ}
    {baseLetter : G} (hbase : baseLetter ∈ E.rel.base) {eps : ℕ}
    {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hadj : ExactPublishedAdjacentGapOutput E adjacentC
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hadjRho : adjacentC * 4 ≤ designRho)
    (hadjEps : adjacentC * 4 ≤ epsD)
    (hepsRho : epsD ≤ designRho)
    (hgap : ExactPublishedGapOutput E gapC
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hgapRho : gapC * 4 ≤ designRho) (hgapEps : gapC * 4 ≤ epsD)
    {u u' v : List (GGT.RelLetter G Bool)}
    (hp : RelWord.IsPrimePiece E.rel
      (RelWord.symmetrized
        (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms))
      eps u u' v) :
    max u.length u'.length ≤ [baseLetter].length +
      blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 6 := by
  rcases hp with ⟨hv, middle, tail, hsplit, y, z, hy, hz, hval | hval⟩
  · have hdirect := directPrime_lengths_le_of_exactDesign E hN hbase hdesign
      hcount heven hW hgap hgapRho hgapEps
      (RelWord.mem_symmetrized.mp hv) hsplit hy hz hval
    simp only [blockConst, blockSeparation, List.length_singleton] at hdirect ⊢
    omega
  · exact inversePrime_lengths_le_of_exactDesign E hN hbase hdesign
      hcount heven hW hadj hadjRho hadjEps hepsRho
      (RelWord.mem_symmetrized.mp hv) hsplit hy hz hval

/-- **The long-prefix conclusion at one exact relator design.**

This is the geometric body of the separation producer, with the chosen list
and its exact avoidance certificates exposed and with no `w' ≠ w` premise.
That omission is essential for Hull's same-word published pieces. -/
theorem listVal_conj_of_exactDesign_long_prefixes
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N)
    {epsD adjacentC designRho diffRadius W target : ℕ}
    {baseLetter : G} (hbase : baseLetter ∈ E.rel.base) {eps : ℕ}
    {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hadj : ExactPublishedAdjacentGapOutput E adjacentC
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hadjRho : adjacentC * 4 ≤ designRho)
    (hadjEps : adjacentC * 4 ≤ epsD)
    (hepsRho : epsD ≤ designRho)
    {w w' u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) w)
    (hw' : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) w')
    (hu : w = u ++ tl) (hu' : w' = u' ++ tl')
    (hlong : [baseLetter].length +
      blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 6 < u.length)
    {y z : G} (hy : wordNorm E.rel.alphabet.carrier y ≤ eps)
    (hz : wordNorm E.rel.alphabet.carrier z ≤ eps)
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
  have hshort : eps + 2 ≤ blockConst [baseLetter] cw := by
    show eps + 2 ≤ [baseLetter].length + cw
    dsimp only [cw]
    omega
  have hadm : RelWord.IsAdmissible E.rel
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) :=
    isAdmissible_relatorWord₂ (by simpa using hbase) hloxfam ms
  obtain ⟨py, _hpy0, hpylen, hpylet, hpyval, _hpynorm⟩ :=
    exists_side_spelling₂ E hN hy
  obtain ⟨pz, hpz0, hpzlen, hpzlet, hpzval, _hpznorm⟩ :=
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
    dsimp only [cw]
    simp only [blockConst, List.length_singleton] at hc ⊢
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
    dsimp only [cw]
    simp only [blockConst, List.length_singleton] at hc ⊢
    omega
  have hqg := fourGonQG_of_sides E.rel (le_trans hpylen hshort)
    (le_trans hpzlen hshort) hcu hcu'
  have hcapacity : 2 * (py.length + pz.length + 3) + 2 ≤ u.length := by
    have hbaseCapacity := exactPublishedAdjacentCapacity_singleton baseLetter eps
    omega
  have hconj := listVal_conj_of_exactPublished_relativeSides E hdesign hcount
    heven hW hadj hadjRho hadjEps hepsRho hw hw' hu hu' hclose hpz0
    hlet4 hqg hcapacity hqlet hslet
  rw [hpyval] at hconj
  exact hconj

/-- **A same-word published piece of the exact relator is uniformly short.**

If its first exposed prefix crossed the fixed long-prefix threshold, the exact
quadrilateral theorem would give the full-word conjugacy forbidden in the
definition.  Reversing the short connector equation gives the same bound for
the second prefix. -/
theorem sameWordPublishedPiece_lengths_le_of_exactDesign
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N)
    {epsD adjacentC designRho diffRadius W target : ℕ}
    {baseLetter : G} (hbase : baseLetter ∈ E.rel.base) {eps : ℕ}
    {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hadj : ExactPublishedAdjacentGapOutput E adjacentC
      (blockConst [baseLetter] (max 1 (eps + 2))))
    (hadjRho : adjacentC * 4 ≤ designRho)
    (hadjEps : adjacentC * 4 ≤ epsD)
    (hepsRho : epsD ≤ designRho)
    {u u' v : List (GGT.RelLetter G Bool)}
    (hp : RelWord.IsSameWordPublishedPiece E.rel
      (RelWord.symmetrized
        (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms))
      eps u u' v) :
    max u.length u'.length ≤
      [baseLetter].length + blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 6 := by
  rcases hp with ⟨hv, ⟨tl, hu⟩, ⟨tl', hu'⟩,
    y, z, hy, hz, hval, hexcl⟩
  have hvSym := RelWord.mem_symmetrized.mp hv
  have hlu : u.length ≤
      [baseLetter].length + blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 6 := by
    by_contra hnot
    have hlong : [baseLetter].length +
        blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 6 < u.length := by
      omega
    exact hexcl (listVal_conj_of_exactDesign_long_prefixes E hN hbase
      hdesign hcount heven hW hadj hadjRho hadjEps hepsRho
      hvSym hvSym hu hu' hlong hy hz hval)
  have hlu' : u'.length ≤
      [baseLetter].length + blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 6 := by
    by_contra hnot
    have hlong : [baseLetter].length +
        blockSeparation [baseLetter] (max 1 (eps + 2)) eps + 6 < u'.length := by
      omega
    have hyinv : wordNorm E.rel.alphabet.carrier y⁻¹ ≤ eps := by
      rw [wordNorm_inv E.rel.alphabet.symmetricGenerating y]
      exact hy
    have hzinv : wordNorm E.rel.alphabet.carrier z⁻¹ ≤ eps := by
      rw [wordNorm_inv E.rel.alphabet.symmetricGenerating z]
      exact hz
    have hval' : GGT.RelLetter.listVal u =
        y⁻¹ * GGT.RelLetter.listVal u' * z⁻¹ := by
      rw [hval]
      group
    have hconj := listVal_conj_of_exactDesign_long_prefixes E hN hbase
      hdesign hcount heven hW hadj hadjRho hadjEps hepsRho
      hvSym hvSym hu' hu hlong hyinv hzinv hval'
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

section PublishedEndpoint

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- **Hull's published one-relator input from the exact finite-avoidance
design.**

The exponent list is selected only after fixing every geometric constant and
the final length.  Its exact count gives the `(4,1)` quasi-geodesic clause;
the fixed-design same-word and prime-piece theorems give the two published
piece clauses with the same strict real threshold. -/
theorem exists_hullRelatorWord₂OfBaseLetterPublished_exact
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N) (t : G)
    (ht : t⁻¹ ∈ E.rel.base) (eps rho : ℕ) (mu : ℝ) (hmu : 0 < mu) :
    ∃ u ∈ N, ∃ R : List (GGT.RelLetter G Bool),
      GGT.RelLetter.listVal R = t⁻¹ * u ∧
        RelWord.IsLemma49Input E.rel (RelWord.symmetrized R) eps mu rho ∧
          ∀ x, GGT.RelLetter.base x ∈ R → x = t⁻¹ := by
  let p : List G := [t⁻¹]
  let cw := max 1 (eps + 2)
  let sep := blockSeparation p cw eps
  let B := p.length + sep + 6
  obtain ⟨delta, hdelta⟩ :=
    GGT.exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded E.rel E.embedded
  obtain ⟨gapC, _hgapC, hgap⟩ :=
    exists_exactPublishedGapOutput E E.base_inv
      (bn := blockConst p cw) hdelta
  obtain ⟨adjacentC, _hadjacentC, hadj⟩ :=
    exists_exactPublishedAdjacentGapOutput E E.base_inv
      (bn := blockConst p cw) hdelta
  let epsD := max (gapC * 4) (adjacentC * 4)
  obtain ⟨n, hn⟩ := exists_nat_gt ((B : ℝ) / mu)
  let requestedRho := max rho epsD
  let target := 2 * max (max requestedRho n) 1
  have htarget : 2 ≤ target := by
    dsimp only [target]
    omega
  have hevenTarget : Even target := by
    exact even_two_mul _
  obtain ⟨ms, hdesign, hcount, -⟩ :=
    exists_exactRelatorDesign₂_with_count_one E t⁻¹ ht hdelta
      requestedRho epsD epsD target htarget hevenTarget
  let designRho := max requestedRho
    (GGT.OsinComponents.everyEdgeIsolationRadius delta (2 * (target + 1)))
  let R := relatorWord₂ p (E.lox false) (E.lox true) ms
  have hp : p = [t⁻¹] := rfl
  have hadj' : ExactPublishedAdjacentGapOutput E adjacentC
      (blockConst [t⁻¹] (max 1 (eps + 2))) := by
    simpa only [p, cw] using hadj
  have hdesign' : ExactRelatorDesign₂ E t⁻¹ designRho epsD epsD
      (target + 1) target ms := by
    simpa only [designRho, requestedRho] using hdesign
  have heven : Even ms.length := by
    rw [hdesign'.1]
    exact hevenTarget
  have hW : 1 + blockConst [t⁻¹] 1 ≤ target + 1 := by
    simp only [blockConst, List.length_singleton]
    omega
  have hgapRho : gapC * 4 ≤ designRho := by
    exact le_trans (le_trans (Nat.le_max_left (gapC * 4) (adjacentC * 4))
      (Nat.le_max_right rho epsD))
      (Nat.le_max_left requestedRho _)
  have hgapEps : gapC * 4 ≤ epsD := Nat.le_max_left _ _
  have hadjRho : adjacentC * 4 ≤ designRho := by
    exact le_trans (le_trans (Nat.le_max_right (gapC * 4) (adjacentC * 4))
      (Nat.le_max_right rho epsD)) (Nat.le_max_left requestedRho _)
  have hadjEps : adjacentC * 4 ≤ epsD := Nat.le_max_right _ _
  have hepsRho : epsD ≤ designRho :=
    le_trans (Nat.le_max_right rho epsD) (Nat.le_max_left requestedRho _)
  have hBreal : (B : ℝ) < mu * (R.length : ℝ) := by
    have h1 : (B : ℝ) < (n : ℝ) * mu := by
      rw [div_lt_iff₀ hmu] at hn
      exact hn
    have hnTarget : n ≤ target := by
      dsimp only [target]
      omega
    have hnR : n ≤ R.length := by
      dsimp only [R]
      rw [length_relatorWord₂, hdesign'.1]
      omega
    have hnR' : (n : ℝ) ≤ (R.length : ℝ) := by exact_mod_cast hnR
    have hmul : (n : ℝ) * mu ≤ (R.length : ℝ) * mu :=
      mul_le_mul_of_nonneg_right hnR' (le_of_lt hmu)
    calc
      (B : ℝ) < (n : ℝ) * mu := h1
      _ ≤ (R.length : ℝ) * mu := hmul
      _ = mu * (R.length : ℝ) := mul_comm _ _
  have hadm : RelWord.IsAdmissible E.rel R := by
    dsimp only [R, p]
    exact isAdmissible_relatorWord₂ (by simpa using ht)
      (fun b => by rw [E.fam_eq]; exact E.lox_mem b) ms
  have hlongrho : rho ≤ R.length := by
    dsimp only [R, p]
    rw [length_relatorWord₂, hdesign'.1]
    dsimp only [target, requestedRho]
    omega
  have hdeep : ∀ a ∈ R, ∀ lam : Bool, GGT.RelLetter.IsCompOf lam a →
      a.val ∉ E.rel.relBall lam rho ∧ (a.val)⁻¹ ∉ E.rel.relBall lam rho := by
    intro a ha lam hcomp
    dsimp only [R, p] at ha
    rcases mem_relatorWord₂ ha with ⟨g, _hg, rfl⟩ | ⟨b, m, hm, rfl⟩
    · exact False.elim hcomp
    · have hbl : b = lam := hcomp
      rw [← hbl]
      rw [ite_lox_eq E b]
      exact ⟨notMem_relBall_of_le
          (le_trans (Nat.le_max_left rho epsD) (Nat.le_max_left requestedRho _))
          (hdesign'.2.2.1 m hm b b).1,
        notMem_relBall_of_le
          (le_trans (Nat.le_max_left rho epsD) (Nat.le_max_left requestedRho _))
          (hdesign'.2.2.1 m hm b b).2⟩
  have hlongMatch : ∀ w w' u u' : List (GGT.RelLetter G Bool),
      RelWord.Sym R w → RelWord.Sym R w' → w' ≠ w →
      (∃ tl, w = u ++ tl) → (∃ tl', w' = u' ++ tl') →
      B < u.length → ∀ y z : G,
      wordNorm E.rel.alphabet.carrier y ≤ eps → wordNorm E.rel.alphabet.carrier z ≤ eps →
      GGT.RelLetter.listVal u' = y * GGT.RelLetter.listVal u * z →
      GGT.RelLetter.listVal w' = y * GGT.RelLetter.listVal w * y⁻¹ := by
    intro w w' u u' hw hw' _hne ⟨tl, htl⟩ ⟨tl', htl'⟩ hu y z hy hz hval
    apply listVal_conj_of_exactDesign_long_prefixes (eps := eps)
      E hN ht hdesign' hcount heven hW hadj'
    · exact hadjRho
    · exact hadjEps
    · exact hepsRho
    · simpa only [R, p] using hw
    · simpa only [R, p] using hw'
    · exact htl
    · exact htl'
    · simpa only [B, sep, p, cw] using hu
    · exact hy
    · exact hz
    · exact hval
  have hsc : RelWord.IsSmallCancellation E.rel (RelWord.symmetrized R)
      eps mu rho :=
    RelWord.isSmallCancellation_symmetrized_of_longMatch_ne E.base_inv hadm
      hlongrho hdeep hlongMatch hBreal
  have hqg : ∀ v ∈ RelWord.symmetrized R,
      GGT.IsQuasiGeodesicChainAt E.rel.alphabet.carrier 4 1
        (fun i => GGT.RelLetter.listVal (v.take i)) v.length := by
    intro v hv
    apply quasiGeodesic_sym_of_blockCountAt₂ E ht hcount v
    simpa only [R, p] using RelWord.mem_symmetrized.mp hv
  have hsame : ∀ u u' v,
      RelWord.IsSameWordPublishedPiece E.rel (RelWord.symmetrized R) eps u u' v →
        max (u.length : ℝ) (u'.length : ℝ) < mu * v.length := by
    intro u u' v hv
    have hnat := sameWordPublishedPiece_lengths_le_of_exactDesign (eps := eps)
      E hN ht hdesign' hcount heven hW
      hadj' hadjRho hadjEps hepsRho
      (by simpa only [R, p] using hv)
    have hle : max (u.length : ℝ) (u'.length : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast hnat
    have hvlen : v.length = R.length :=
      RelWord.Sym.length_eq (RelWord.mem_symmetrized.mp hv.1)
    rw [hvlen]
    exact lt_of_le_of_lt hle hBreal
  have hpublished : ∀ u u' v,
      RelWord.IsPublishedPiece E.rel (RelWord.symmetrized R) eps u u' v →
        max (u.length : ℝ) (u'.length : ℝ) < mu * v.length :=
    RelWord.publishedPiecesSmall_symmetrized_of_piecesSmall_of_sameWord hsc hsame
  have hprime : ∀ u u' v,
      RelWord.IsPrimePiece E.rel (RelWord.symmetrized R) eps u u' v →
        max (u.length : ℝ) (u'.length : ℝ) < mu * v.length := by
    intro u u' v hv
    have hgap' : ExactPublishedGapOutput E gapC
        (blockConst [t⁻¹] (max 1 (eps + 2))) := by
      change ExactPublishedGapOutput E gapC
        (blockConst [t⁻¹] (max 1 (eps + 2))) at hgap
      exact hgap
    have hnat := primePiece_lengths_le_of_exactDesign (eps := eps)
      E hN ht hdesign' hcount heven hW hadj'
      hadjRho hadjEps hepsRho hgap' hgapRho hgapEps
      (by simpa only [R, p] using hv)
    have hle : max (u.length : ℝ) (u'.length : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast hnat
    have hvlen : v.length = R.length :=
      RelWord.Sym.length_eq (RelWord.mem_symmetrized.mp hv.1)
    rw [hvlen]
    exact lt_of_le_of_lt hle hBreal
  have humem : GGT.RelLetter.listVal
      (blockWord (E.lox false) (E.lox true) false ms) ∈ N := by
    refine listVal_blockWord_mem E.le ?_ false ms
    intro b
    rw [ite_lox_eq E b]
    exact E.lox_mem b
  refine ⟨GGT.RelLetter.listVal
      (blockWord (E.lox false) (E.lox true) false ms), humem, R, ?_, ?_, ?_⟩
  · dsimp only [R, p]
    rw [listVal_relatorWord₂]
    simp
  · exact RelWord.isLemma49Input_symmetrized_of E.rel R eps mu rho hsc hqg
      hpublished hprime
  · intro x hx
    dsimp only [R, p] at hx
    rcases mem_relatorWord₂ hx with ⟨g, hg, hgx⟩ | ⟨b, m, hm, hmx⟩
    · have hgt : g = t⁻¹ := by simpa only [List.mem_singleton] using hg
      have hxg : x = g := congrArg GGT.RelLetter.val hgx
      exact hxg.trans hgt
    · cases hmx

end PublishedEndpoint

end HullSC
end GroupApproximation
