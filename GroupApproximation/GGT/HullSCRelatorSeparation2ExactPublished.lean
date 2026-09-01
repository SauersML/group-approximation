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
