import GroupApproximation.Leavitt.UniversalOneSidedPairRing
import GroupApproximation.Leavitt.OneSidedCompressorDefect
import GroupApproximation.Leavitt.FullIdempotentNormalGeneration
import GroupApproximation.Leavitt.ElementaryNormalGeneration
import GroupApproximation.Leavitt.ElementaryWeylMonomial
import GroupApproximation.Meta.AxiomGuard

/-!
# The normal closure of `d` in `EL₄(𝒞)` is everything

`non_mf_groups_exist.tex`, proof of Theorem `thm:full-defect-ring`, *The universal
group*, lines 957--976:

> By Lemma~\ref{lem:ring-compression-cell} there are $u,c\in G$ with
> $uLu^{-1}\le L$, $c\in C_G(L)$, and
> \[ d=[ucu^{-1},e_{23}(1)]=e_{13}(e)\in\mathfrak D_G(L). \]
>
> Let $N$ be the normal closure of $d$ in $G$.  For arbitrary $a,b\in\mathcal C$,
> the Steinberg relations give
> \[ [e_{41}(a),e_{13}(e)]=e_{43}(ae),\qquad [e_{43}(ae),e_{32}(b)]=e_{42}(aeb). \]
> So $e_{42}(1)=e_{42}(t_1es_1)\in N$.
> Elementary signed permutation matrices conjugate this element to every
> off-diagonal position, up to a sign, so $e_{ij}(1)\in N$ whenever $i\ne j$.
> For distinct $i,j,k$ and every $r\in\mathcal C$,
> \[ [e_{ij}(1),e_{jk}(r)]=e_{ik}(r)\in N. \]
> So $N=G$, and $\mathfrak D_G(L)=G$.

Here `G = EL₄(𝒞)` over the universal pair ring `𝒞 = UniversalPair.UniversalPairRing`,
and `L = core 𝒞 = EL₃(𝒞)` sits on coordinates `1,2,3` (`coreIdx 0,1,2`). Coordinate
`4` is `lastIdx`, `s = s₀`, `t = t₀`, and `e = 1 - st` is
`UniversalPair.pairInverse.e`. `𝔇_G(L)` is `Manuscript.OneSidedMFRadical.printedDefect`.

Proof route.
* `u` and `c` are `compressor` and `centralMark`. `defect_eq` gives
  `d = [ucu⁻¹, e₂₃(1)] = e₁₃(e)`.
* `N` is defined literally as the normal closure of `[ucu⁻¹, e₂₃(1)]`.
* `e₄₂(1) ∈ N`: take `a = t₁` and `b = s₁` in the two printed Steinberg
  commutators, then apply `t₁ e s₁ = 1` (`printedFullnessWitness`).
* `e_ij(1) ∈ N`: signed Weyl conjugation (`ElementaryWeyl.elGen_one_mem_of_ne`).
* `e_ik(r) ∈ N`: the Steinberg relation `[e_ij(1), e_jk(r)] = e_ik(r)`.
* `N = G`: `elementaryGroup_normal_eq_top_of_elementaryRoot_mem`, applied to
  `e₄₂(1)`. Then `𝔇_G(L) = G`, because `N ≤ 𝔇_G(L)`: the defect is normal and
  contains `d`.
-/

namespace GroupApproximation.Manuscript.NonMF.AuditOneSided1

open GroupApproximation.OneSidedCompressor
open scoped commutatorElement

/-- tex 957--961: in `G = EL₄(𝒞)` with `L = EL₃(𝒞)` on coordinates `1,2,3`,
there are `u, c ∈ G` with `uLu⁻¹ ≤ L` and `c ∈ C_G(L)`. Also
`d = [ucu⁻¹, e₂₃(1)] = e₁₃(e)`, and `d ∈ 𝔇_G(L)`. -/
theorem manuscriptSentence_universalCompressionCellDefect :
    ∃ u c : elementaryGroup (Fin 4) UniversalPair.UniversalPairRing,
      (∀ g ∈ core UniversalPair.UniversalPairRing,
          u * g * u⁻¹ ∈ core UniversalPair.UniversalPairRing) ∧
        (∀ g ∈ core UniversalPair.UniversalPairRing, Commute c g) ∧
        ⁅u * c * u⁻¹,
            elementaryRoot (coreIdx 1) (coreIdx 2) (coreIdx_injective.ne oneNeTwo)
              (1 : UniversalPair.UniversalPairRing)⁆ =
          elementaryRoot (coreIdx 0) (coreIdx 2) (coreIdx_injective.ne zeroNeTwo)
            UniversalPair.pairInverse.e ∧
        elementaryRoot (coreIdx 0) (coreIdx 2) (coreIdx_injective.ne zeroNeTwo)
            UniversalPair.pairInverse.e ∈
          GroupApproximation.Manuscript.OneSidedMFRadical.printedDefect
            (core UniversalPair.UniversalPairRing) :=
  ⟨compressor UniversalPair.pairInverse, centralMark UniversalPair.pairInverse,
    compressor_compresses_core UniversalPair.pairInverse,
    centralMark_commute_core UniversalPair.pairInverse,
    defect_eq UniversalPair.pairInverse,
    printedDefectRoot_mem_printedDefect UniversalPair.pairInverse⟩

#audit_axioms manuscriptSentence_universalCompressionCellDefect

/-- tex 963: `N`, the normal closure in `G = EL₄(𝒞)` of
`d = [ucu⁻¹, e₂₃(1)]`, with `u` the compressor and `c` the central mark. -/
noncomputable def printedN :
    Subgroup (elementaryGroup (Fin 4) UniversalPair.UniversalPairRing) :=
  Subgroup.normalClosure
    {⁅compressor UniversalPair.pairInverse * centralMark UniversalPair.pairInverse *
        (compressor UniversalPair.pairInverse)⁻¹,
      printedEll UniversalPair.UniversalPairRing⁆}

instance printedN_normal : printedN.Normal :=
  Subgroup.normalClosure_normal

/-- `d = e₁₃(e)` lies in `N`. -/
theorem printedDefectRoot_mem_printedN :
    printedDefectRoot UniversalPair.pairInverse ∈ printedN := by
  rw [← defect_eq UniversalPair.pairInverse]
  exact Subgroup.subset_normalClosure (Set.mem_singleton _)

/-- tex 963: `N` is the normal closure of `d`, and `d = e₁₃(e) ∈ N`. -/
theorem manuscriptSentence_normalClosureOfD :
    printedN = Subgroup.normalClosure
        {⁅compressor UniversalPair.pairInverse * centralMark UniversalPair.pairInverse *
            (compressor UniversalPair.pairInverse)⁻¹,
          printedEll UniversalPair.UniversalPairRing⁆} ∧
      printedDefectRoot UniversalPair.pairInverse ∈ printedN :=
  ⟨rfl, printedDefectRoot_mem_printedN⟩

#audit_axioms manuscriptSentence_normalClosureOfD

/-- tex 969: `e₄₂(1) = e₄₂(t₁ e s₁)`, and this element lies in `N`. -/
theorem manuscriptSentence_e42OneMemN :
    elementaryRoot lastIdx (coreIdx 1) (last_ne_coreIdx 1)
          (1 : UniversalPair.UniversalPairRing) =
        elementaryRoot lastIdx (coreIdx 1) (last_ne_coreIdx 1)
          (UniversalPair.unit.w 1 * UniversalPair.pairInverse.e *
            UniversalPair.unit.v 1) ∧
      elementaryRoot lastIdx (coreIdx 1) (last_ne_coreIdx 1)
          (1 : UniversalPair.UniversalPairRing) ∈ printedN := by
  have h1 : elementaryRoot lastIdx (coreIdx 2) (last_ne_coreIdx 2)
      (UniversalPair.unit.w 1 * UniversalPair.pairInverse.e) ∈ printedN := by
    rw [← elementaryRoot_commutator lastIdx (coreIdx 0) (coreIdx 2)
      (last_ne_coreIdx 0) (coreIdx_injective.ne zeroNeTwo) (last_ne_coreIdx 2)
      (UniversalPair.unit.w 1) UniversalPair.pairInverse.e]
    exact FullIdempotent.commutator_mem_of_right printedN
      (elementaryRoot lastIdx (coreIdx 0) (last_ne_coreIdx 0) (UniversalPair.unit.w 1))
      printedDefectRoot_mem_printedN
  have h2 : elementaryRoot lastIdx (coreIdx 1) (last_ne_coreIdx 1)
      (UniversalPair.unit.w 1 * UniversalPair.pairInverse.e *
        UniversalPair.unit.v 1) ∈ printedN := by
    rw [← elementaryRoot_commutator lastIdx (coreIdx 2) (coreIdx 1)
      (last_ne_coreIdx 2) (coreIdx_injective.ne oneNeTwo.symm) (last_ne_coreIdx 1)
      (UniversalPair.unit.w 1 * UniversalPair.pairInverse.e) (UniversalPair.unit.v 1)]
    exact FullIdempotent.commutator_mem_of_left printedN h1
      (elementaryRoot (coreIdx 2) (coreIdx 1) (coreIdx_injective.ne oneNeTwo.symm)
        (UniversalPair.unit.v 1))
  rw [UniversalPair.printedFullnessWitness] at h2
  exact ⟨by rw [UniversalPair.printedFullnessWitness], h2⟩

#audit_axioms manuscriptSentence_e42OneMemN

/-- tex 969: `e_ij(1) ∈ N` for all `i ≠ j`. -/
theorem manuscriptSentence_unitRootsMemN :
    ∀ (i j : Fin 4) (hij : i ≠ j),
      elementaryRoot i j hij (1 : UniversalPair.UniversalPairRing) ∈ printedN :=
  fun _ _ hij =>
    ElementaryWeyl.elGen_one_mem_of_ne printedN (last_ne_coreIdx 1)
      manuscriptSentence_e42OneMemN.2 hij

#audit_axioms manuscriptSentence_unitRootsMemN

/-- tex 969--974: for distinct `i, j, k` and every `r ∈ 𝒞`,
`[e_ij(1), e_jk(r)] = e_ik(r)`, and this element lies in `N`. -/
theorem manuscriptSentence_steinbergSpreadsInN :
    ∀ (i j k : Fin 4) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
      (r : UniversalPair.UniversalPairRing),
      ⁅elementaryRoot i j hij (1 : UniversalPair.UniversalPairRing),
          elementaryRoot j k hjk r⁆ = elementaryRoot i k hik r ∧
        elementaryRoot i k hik r ∈ printedN := by
  intro i j k hij hjk hik r
  have hcomm : ⁅elementaryRoot i j hij (1 : UniversalPair.UniversalPairRing),
      elementaryRoot j k hjk r⁆ = elementaryRoot i k hik r := by
    rw [elementaryRoot_commutator i j k hij hjk hik
      (1 : UniversalPair.UniversalPairRing) r, one_mul]
  refine ⟨hcomm, ?_⟩
  rw [← hcomm]
  exact FullIdempotent.commutator_mem_of_left printedN
    (manuscriptSentence_unitRootsMemN i j hij) (elementaryRoot j k hjk r)

#audit_axioms manuscriptSentence_steinbergSpreadsInN

/-- tex 976: `N = G` and `𝔇_G(L) = G`. -/
theorem manuscriptSentence_normalClosureIsEverything :
    printedN = ⊤ ∧
      GroupApproximation.Manuscript.OneSidedMFRadical.printedDefect
          (core UniversalPair.UniversalPairRing) = ⊤ := by
  have hN : printedN = ⊤ :=
    elementaryGroup_normal_eq_top_of_elementaryRoot_mem (by simp) printedN
      (last_ne_coreIdx 1) manuscriptSentence_e42OneMemN.2 ⟨1, 1, by simp⟩
  have hd : ⁅compressor UniversalPair.pairInverse * centralMark UniversalPair.pairInverse *
        (compressor UniversalPair.pairInverse)⁻¹,
      printedEll UniversalPair.UniversalPairRing⁆ ∈
        GroupApproximation.Manuscript.OneSidedMFRadical.printedDefect
          (core UniversalPair.UniversalPairRing) :=
    GroupApproximation.Manuscript.OneSidedMFRadical.printedDefect_generator_mem
      (core UniversalPair.UniversalPairRing)
      (compressor_compresses_core UniversalPair.pairInverse)
      (centralMark_commute_core UniversalPair.pairInverse) printedEll_mem_core
  have hle : printedN ≤
      GroupApproximation.Manuscript.OneSidedMFRadical.printedDefect
        (core UniversalPair.UniversalPairRing) :=
    Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hd)
  refine ⟨hN, top_unique ?_⟩
  rw [← hN]
  exact hle

#audit_axioms manuscriptSentence_normalClosureIsEverything

end GroupApproximation.Manuscript.NonMF.AuditOneSided1
