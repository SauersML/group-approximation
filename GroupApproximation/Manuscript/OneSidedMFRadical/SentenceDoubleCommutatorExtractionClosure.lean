import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceRootDetectionCompositionClosure

/-!
# Sentence wrappers for double-commutator root extraction

Rows 246--253 of the manuscript are already proved by the sparse and dense
extraction lemmas.  This module adds paper-facing sentence names only; it does
not duplicate their matrix calculations.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

universe u v

variable {ι : Type u} {S : Type v} [Fintype ι] [DecidableEq ι] [Ring S]

/-- **Sentence 246.**  The vanishing inverse-entry configuration makes the
printed double commutator a nontrivial root source inside `N`. -/
theorem manuscriptSentence246_sparseDoubleCommutator_extractsRoot
    (hcard : 3 ≤ Fintype.card ι)
    (N : Subgroup (elementaryGroup ι S)) [N.Normal]
    {g : elementaryGroup ι S} (hg : g ∈ N)
    {j k : ι} (hjk : j ≠ k)
    (hzero : (((g : (Matrix ι ι S)ˣ)⁻¹ : (Matrix ι ι S)ˣ) :
      Matrix ι ι S) j k = 0)
    (hne : ((g : (Matrix ι ι S)ˣ) : Matrix ι ι S) j k ≠ 0) :
    ∃ (p q : ι) (hpq : p ≠ q) (x : S),
      x ≠ 0 ∧ elGen p q hpq x ∈ N :=
  exists_elGen_mem_of_inv_entry_zero hcard N hg hjk hzero hne

/-- **Sentence 247.**  The square-zero, row-supported sparse defect with its
surviving entry yields the same extracted nonzero root. -/
theorem manuscriptSentence247_sparseDefect_extractsRoot
    (hcard : 3 ≤ Fintype.card ι)
    (N : Subgroup (elementaryGroup ι S)) [N.Normal]
    {g : elementaryGroup ι S} (hg : g ∈ N)
    {j k : ι} (hjk : j ≠ k)
    (hzero : (((g : (Matrix ι ι S)ˣ)⁻¹ : (Matrix ι ι S)ˣ) :
      Matrix ι ι S) j k = 0)
    (hne : ((g : (Matrix ι ι S)ˣ) : Matrix ι ι S) j k ≠ 0) :
    ∃ (p q : ι) (hpq : p ≠ q) (x : S),
      x ≠ 0 ∧ elGen p q hpq x ∈ N :=
  manuscriptSentence246_sparseDoubleCommutator_extractsRoot
    hcard N hg hjk hzero hne

/-- **Sentence 248.**  In the dense-entry configuration, coefficient
separation chooses the printed `a,b` and the construction extracts a root. -/
theorem manuscriptSentence248_denseCoefficients_extractRoot
    (hcard : 3 ≤ Fintype.card ι) (L : LeavittFamily S)
    (hdivide : ∀ z : S, z ≠ 0 → ∃ c d : S, c * z * d = 1)
    (N : Subgroup (elementaryGroup ι S)) [N.Normal]
    {g : elementaryGroup ι S} (hg : g ∈ N)
    {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i)
    (hinv : (((g : (Matrix ι ι S)ˣ)⁻¹ : (Matrix ι ι S)ˣ) :
      Matrix ι ι S) j k ≠ 0)
    (hgentry : ((g : (Matrix ι ι S)ˣ) : Matrix ι ι S) l i ≠ 0) :
    ∃ (p q : ι) (hpq : p ≠ q) (x : S),
      x ≠ 0 ∧ elGen p q hpq x ∈ N :=
  exists_elGen_mem_of_dense_entries hcard L hdivide N hg
    hij hkl hjk hli hinv hgentry

/-- **Sentences 249--250.**  The annihilating and reversed-nonzero coefficient
equations are exactly the hypotheses under which the dense double commutator
has a square-zero, row-supported defect and extracts a nonzero root. -/
theorem manuscriptSentences249_250_denseDoubleCommutator_extractsRoot
    (hcard : 3 ≤ Fintype.card ι)
    (N : Subgroup (elementaryGroup ι S)) [N.Normal]
    {g : elementaryGroup ι S} (hg : g ∈ N)
    {i j k l m : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) {a b : S}
    (hzero : a * (((g : (Matrix ι ι S)ˣ)⁻¹ : (Matrix ι ι S)ˣ) :
      Matrix ι ι S) j k * b = 0)
    (hne : b * ((g : (Matrix ι ι S)ˣ) : Matrix ι ι S) l i * a *
      (((g : (Matrix ι ι S)ˣ)⁻¹ : (Matrix ι ι S)ˣ) :
        Matrix ι ι S) j m ≠ 0) :
    ∃ (p q : ι) (hpq : p ≠ q) (x : S),
      x ≠ 0 ∧ elGen p q hpq x ∈ N :=
  exists_elGen_mem_of_annihilating_coefficients hcard N hg
    hij hkl hjk hli hzero hne

/-- **Sentence 251.**  A square-zero one-row unipotent in a normal subgroup,
with one nonzero row entry, yields the displayed elementary root. -/
theorem manuscriptSentence251_rowExtraction
    (hcard : 3 ≤ Fintype.card ι)
    (N : Subgroup (elementaryGroup ι S)) [N.Normal]
    {z : elementaryGroup ι S} (hz : z ∈ N)
    {v : Matrix ι ι S} {k : ι}
    (hv : IsRowSupported v k) (hsq : v * v = 0)
    (hzv : (z : (Matrix ι ι S)ˣ) = sqZeroUnit v hsq)
    {m : ι} (hvm : v k m ≠ 0) :
    ∃ (p q : ι) (hpq : p ≠ q) (x : S),
      x ≠ 0 ∧ elGen p q hpq x ∈ N :=
  exists_elGen_mem_of_row_supported_sq_zero
    hcard N hz hv hsq hzv hvm

/-- **Sentence 252.**  In the exact rank-twelve group, the extracted nonzero
root normally generates, and the completed root detection proves simplicity. -/
theorem manuscriptSentence252_extractedRoot_closesSimplicity
    (N : Subgroup RankTwelveEndpoint.H) (hN : N.Normal)
    (i j : Fin 12) (hij : i ≠ j) (a : RankTwelveEndpoint.R)
    (ha : a ≠ 0)
    (hmem : elementaryRoot i j hij a ∈ N) :
    N = ⊤ ∧ IsSimpleGroup RankTwelveEndpoint.H :=
  ⟨RankTwelveEndpoint.normal_eq_top_of_nonzero_elementaryRoot_mem
      N hN i j hij a ha hmem,
    RankTwelveEndpoint.manuscriptPropositionSimple⟩

/-- **Sentence 253.**  The explicit unit-coefficient root is nonidentity, and
hence the exact manuscript group is nontrivial. -/
theorem manuscriptSentence253_explicitNontrivialRoot :
    elementaryRoot (R := RankTwelveEndpoint.R)
        (0 : Fin 12) 1 (by decide) 1 ≠ 1 ∧
      Nontrivial RankTwelveEndpoint.H := by
  constructor
  · intro hroot
    have hzero : (1 : RankTwelveEndpoint.R) = 0 :=
      (RankTwelveEndpoint.elementaryRoot_eq_one_iff
        (0 : Fin 12) 1 (by decide) 1).mp hroot
    exact one_ne_zero hzero
  · exact RankTwelveEndpoint.nontrivial

end OneSidedMFRadical
end Manuscript
end GroupApproximation
