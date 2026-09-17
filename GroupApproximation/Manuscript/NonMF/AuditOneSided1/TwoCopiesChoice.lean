import GroupApproximation.Manuscript.NonMFSentences.FullDefectIdealGloss
import GroupApproximation.Leavitt.ProperlyInfiniteUnit
import GroupApproximation.Leavitt.UniversalOneSidedPairRing
import GroupApproximation.Leavitt.ElementaryRoots
import GroupApproximation.Meta.AxiomGuard

/-!
# Fullness gives two copies, and the universal ring maps onto them

`non_mf_groups_exist.tex`, proof of Lemma `lem:two-copies`, line 818:

> Put $e=1-st$, so that $es=te=0$, and choose $a_j,b_j\in R$, $0\le j<m$, with
> $\sum_ja_jeb_j=1$.

Proof of Theorem `thm:full-defect-ring`, *Rank two*, lines 980--984:

> Now let $R$ satisfy the hypothesis.  By Lemma~\ref{lem:two-copies} choose
> $v_0,v_1,w_0,w_1\in R$ with $w_iv_j=\delta_{ij}$.  Then
> $\varphi\colon s_i\mapsto v_i$, $t_i\mapsto w_i$ is a unital ring homomorphism
> $\mathcal C\to R$, and it induces a homomorphism $\EL_4(\mathcal C)\to\EL_4(R)$.

The hypothesis is the printed one: `ts = 1` and the two-sided ideal `R(1-st)R`
is all of `R`.

Proof route.
* Line 818. `es = 0` and `te = 0` are ring algebra from `ts = 1`. The witnesses
  `a_j, b_j` come from `span_singleton_eq_top_iff_exists_sum`, which turns the
  ideal form `R(1-st)R = R` into finite sums.
* Line 980, choice. `RankDescent.ofFull` builds the four elements with
  `w_i v_j = δ_ij` from the witnesses, and it takes `R(1-st)R = R` in the
  finite-sum form.
* Line 980, the maps.
  - `φ` is `UniversalPair.lift` of the chosen family, with its values on the
    generators given by `lift_v` and `lift_w`.
  - The induced map is `elementaryGroupMap φ`, and on roots it is the
    entrywise image (`elementaryMatrixUnitMap_elementaryUnit`).
-/

namespace GroupApproximation.Manuscript.NonMF.AuditOneSided1

open scoped BigOperators

/-- tex 818: with `e = 1 - st` we have `es = te = 0`, and `R(1-st)R = R` gives
finitely many `a_j, b_j` with `∑_j a_j e b_j = 1`. -/
theorem manuscriptSentence_twoCopiesPutEAndChooseWitnesses {R : Type*} [Ring R]
    (s t : R) (hts : t * s = 1)
    (hfull : TwoSidedIdeal.span ({1 - s * t} : Set R) = ⊤) :
    (1 - s * t) * s = 0 ∧ t * (1 - s * t) = 0 ∧
      ∃ (m : ℕ) (a b : Fin m → R), ∑ j, a j * (1 - s * t) * b j = 1 := by
  refine ⟨?_, ?_,
    (NonMFSentences.FullDefectIdealGloss.span_singleton_eq_top_iff_exists_sum
      (1 - s * t)).mp hfull⟩
  · rw [sub_mul, one_mul, mul_assoc, hts, mul_one, sub_self]
  · rw [mul_sub, mul_one, ← mul_assoc, hts, one_mul, sub_self]

#audit_axioms manuscriptSentence_twoCopiesPutEAndChooseWitnesses

/-- tex 980: when `ts = 1` and `R(1-st)R = R`, Lemma `lem:two-copies` gives
`v₀, v₁, w₀, w₁ ∈ R` with `w_i v_j = δ_ij`. -/
theorem manuscriptSentence_rankTwoChooseTwoCopies {R : Type*} [Ring R]
    (s t : R) (hts : t * s = 1)
    (hfull : TwoSidedIdeal.span ({1 - s * t} : Set R) = ⊤) :
    ∃ v w : Fin 2 → R, ∀ i j : Fin 2, w i * v j = if i = j then 1 else 0 := by
  obtain ⟨m, a, b, hab⟩ :=
    (NonMFSentences.FullDefectIdealGloss.span_singleton_eq_top_iff_exists_sum
      (1 - s * t)).mp hfull
  have Q : GroupApproximation.RankDescent.ProperlyInfiniteUnit R :=
    GroupApproximation.RankDescent.ofFull
      (⟨s, t, hts⟩ : GroupApproximation.OneSidedCompressor.OneSidedInverse R)
      (m := m) a b hab
  exact ⟨Q.v, Q.w, Q.w_mul_v⟩

#audit_axioms manuscriptSentence_rankTwoChooseTwoCopies

/-- tex 980--984: given `v₀, v₁, w₀, w₁ ∈ R` with `w_i v_j = δ_ij`, there is a
(unital) ring homomorphism `φ : 𝒞 → R` with `s_i ↦ v_i` and `t_i ↦ w_i`. It
induces a group homomorphism `EL₄(𝒞) → EL₄(R)` that sends each elementary root
`e_ij(a)` to `e_ij(φ a)`. -/
theorem manuscriptSentence_universalRingHomInducesEL4 {R : Type*} [Ring R]
    (v w : Fin 2 → R) (hvw : ∀ i j : Fin 2, w i * v j = if i = j then 1 else 0) :
    ∃ φ : UniversalPair.UniversalPairRing →+* R,
      (∀ i : Fin 2, φ (UniversalPair.unit.v i) = v i ∧
        φ (UniversalPair.unit.w i) = w i) ∧
      ∃ Φ : elementaryGroup (Fin 4) UniversalPair.UniversalPairRing →*
          elementaryGroup (Fin 4) R,
        ∀ (i j : Fin 4) (hij : i ≠ j) (a : UniversalPair.UniversalPairRing),
          Φ (elementaryRoot i j hij a) = elementaryRoot i j hij (φ a) := by
  refine ⟨(UniversalPair.lift
      (⟨v, w, hvw⟩ : GroupApproximation.RankDescent.ProperlyInfiniteUnit R)).toRingHom,
    fun i => ⟨UniversalPair.lift_v
        (⟨v, w, hvw⟩ : GroupApproximation.RankDescent.ProperlyInfiniteUnit R) i,
      UniversalPair.lift_w
        (⟨v, w, hvw⟩ : GroupApproximation.RankDescent.ProperlyInfiniteUnit R) i⟩,
    elementaryGroupMap (UniversalPair.lift
      (⟨v, w, hvw⟩ : GroupApproximation.RankDescent.ProperlyInfiniteUnit R)).toRingHom,
    fun i j hij a => ?_⟩
  apply Subtype.ext
  exact elementaryMatrixUnitMap_elementaryUnit (UniversalPair.lift
    (⟨v, w, hvw⟩ : GroupApproximation.RankDescent.ProperlyInfiniteUnit R)).toRingHom
    i j hij a

#audit_axioms manuscriptSentence_universalRingHomInducesEL4

end GroupApproximation.Manuscript.NonMF.AuditOneSided1
