import GroupApproximation.Analysis.SoficHyperlinearBridge
import GroupApproximation.Analysis.TracialUltraproductCStar

/-!
# `thm:trace` through the manuscript's ultraproduct

Proof-ledger row `TR.05`.  The printed proof of the trace theorem reads: fix a
free ultrafilter `ω`, form the tracial quotient
`∏ M_{d_n} / ⊕_{2,ω} M_{d_n}`, extend the permutation models to a
`⋆`-homomorphism `π` out of `C*_max(E)` by the universal property, and observe
`τ_E = tr ∘ π`; hence `τ_E` is a hyperlinear trace.

`ShulmanTrace.canonicalMaximalTrace_isHyperlinearTrace_of_isSofic` proves the
conclusion, and proves it along ordinary `atTop`: the same construction, in the
`atTop` tracial matrix quotient, with no ultrafilter anywhere.  `atTop` is the
stronger hypothesis to discharge, so the Lean statement is not weaker -- but it
is a different intermediate object, and the ledger's standard counts that as a
mismatch.  This file removes the mismatch by building the printed intermediate
and running the printed factorization in it.

## Why this is short

`Analysis/TracialMatrixUltraproduct` is already stated over an arbitrary
filter, and so are the C-star instances of `Analysis/TracialQuotientCStar`; the
ultratrace `tr_ω` and its bundling `ultratraceCLM` are already stated at an
ultrafilter.  What was hardwired to `atTop` was only the sofic unitary
representation `ShulmanTrace.soficUnitaryHom`.

A free ultrafilter refines `atTop` on `ℕ` (`Nat.cofinite_eq_atTop`), so every
`atTop`-null defect of the sofic approximation is `ω`-null, and the same
construction goes through verbatim at `ω`.  With that in hand the printed
factorization is one application of
`canonicalMaximalTrace_factorsThrough`, whose hypotheses are exactly the
printed ones: `tr_ω 1 = 1`, and `tr_ω` kills the class of `σ_n(g)` for
`g ≠ 1`, which is the sofic fixed-point count read along `ω`.

The `atTop` route is untouched and still proves the same conclusion; the two
differ only in the quotient the representation lands in, and the endpoint below
carries both, so a reader can see that the printed object and the printed
conclusion are certified together.
-/

namespace GroupApproximation
namespace ShulmanTrace

open Filter Matrix TracialUltraproduct SoficPermutationTrace
open scoped Matrix.Norms.L2Operator

noncomputable section

section UltrafilterModel

variable {G : Type*} [Group G] (S : SoficApproximation G)
variable [∀ n, Nonempty (S.model n)] (ω : Ultrafilter ℕ)

/-- A free ultrafilter on `ℕ` refines `atTop`.  This is the only property of
`ω` the construction below uses. -/
theorem coe_ultrafilter_le_atTop (hω : (ω : Filter ℕ) ≤ Filter.cofinite) :
    (ω : Filter ℕ) ≤ atTop := by
  rw [← Nat.cofinite_eq_atTop]
  exact hω

/-- The class of a sofic unitary sequence is unitary in the `ω`-quotient.
Each coordinate is exactly unitary, so both defects vanish identically and no
property of the filter is used. -/
theorem mk_soficUnitarySeq_mem_unitary_ultrafilter (g : G) :
    tracialMatrixQuotientMk (fun n ↦ S.model n) (ω : Filter ℕ)
        (soficUnitarySeq S g)
      ∈ unitary (TracialMatrixQuotient (fun n ↦ S.model n)
        (ω : Filter ℕ)) := by
  have hstar : star (tracialMatrixQuotientMk (fun n ↦ S.model n)
        (ω : Filter ℕ) (soficUnitarySeq S g))
      = tracialMatrixQuotientMk (fun n ↦ S.model n) (ω : Filter ℕ)
        (star (soficUnitarySeq S g)) :=
    tracialMatrixQuotient_star_mk (fun n ↦ S.model n) (ω : Filter ℕ)
      (soficUnitarySeq S g)
  rw [Unitary.mem_iff, hstar, ← map_mul, ← map_mul]
  constructor
  · have hnull : IsHilbertSchmidtNull (fun n ↦ S.model n) (ω : Filter ℕ)
        (star (soficUnitarySeq S g) * soficUnitarySeq S g - 1) := by
      refine isHilbertSchmidtNull_of_forall_eq_zero fun n ↦ ?_
      rw [modelSeq_sub_apply, modelSeq_mul_apply, modelSeq_star_apply,
        modelSeq_one_apply, soficUnitarySeq_apply]
      have hu := Matrix.mem_unitaryGroup_iff'.mp
        (modelUnitary_mem_unitaryGroup S n g)
      rw [hu, sub_self]
    have := mk_eq_mk_of_isHilbertSchmidtNull (X := fun n ↦ S.model n)
      (l := (ω : Filter ℕ)) hnull
    rw [this, map_one]
  · have hnull : IsHilbertSchmidtNull (fun n ↦ S.model n) (ω : Filter ℕ)
        (soficUnitarySeq S g * star (soficUnitarySeq S g) - 1) := by
      refine isHilbertSchmidtNull_of_forall_eq_zero fun n ↦ ?_
      rw [modelSeq_sub_apply, modelSeq_mul_apply, modelSeq_star_apply,
        modelSeq_one_apply, soficUnitarySeq_apply]
      have hu := Matrix.mem_unitaryGroup_iff.mp
        (modelUnitary_mem_unitaryGroup S n g)
      rw [hu, sub_self]
    have := mk_eq_mk_of_isHilbertSchmidtNull (X := fun n ↦ S.model n)
      (l := (ω : Filter ℕ)) hnull
    rw [this, map_one]

/-- **The sofic unitary representation, in the printed `ω`-quotient.**  The
identity and multiplicativity defects are `‖·‖₂`-null along `atTop`, hence
along the finer filter `ω`, so the quotient forgets them exactly as it does at
`atTop`. -/
def soficUnitaryHomUltrafilter (hω : (ω : Filter ℕ) ≤ Filter.cofinite) :
    G →* unitary (TracialMatrixQuotient (fun n ↦ S.model n)
      (ω : Filter ℕ)) where
  toFun g := ⟨tracialMatrixQuotientMk (fun n ↦ S.model n) (ω : Filter ℕ)
      (soficUnitarySeq S g),
    mk_soficUnitarySeq_mem_unitary_ultrafilter S ω g⟩
  map_one' := by
    apply Subtype.ext
    show tracialMatrixQuotientMk (fun n ↦ S.model n) (ω : Filter ℕ)
        (soficUnitarySeq S 1) = 1
    have hnull : IsHilbertSchmidtNull (fun n ↦ S.model n) (ω : Filter ℕ)
        (soficUnitarySeq S 1 - 1) :=
      Filter.Tendsto.mono_left (isHilbertSchmidtNull_soficUnitarySeq_one S)
        (coe_ultrafilter_le_atTop ω hω)
    have := mk_eq_mk_of_isHilbertSchmidtNull (X := fun n ↦ S.model n)
      (l := (ω : Filter ℕ)) hnull
    rw [this, map_one]
  map_mul' g h := by
    apply Subtype.ext
    show tracialMatrixQuotientMk (fun n ↦ S.model n) (ω : Filter ℕ)
        (soficUnitarySeq S (g * h))
      = tracialMatrixQuotientMk (fun n ↦ S.model n) (ω : Filter ℕ)
          (soficUnitarySeq S g) *
        tracialMatrixQuotientMk (fun n ↦ S.model n) (ω : Filter ℕ)
          (soficUnitarySeq S h)
    have hnull : IsHilbertSchmidtNull (fun n ↦ S.model n) (ω : Filter ℕ)
        (soficUnitarySeq S (g * h) -
          soficUnitarySeq S g * soficUnitarySeq S h) :=
      Filter.Tendsto.mono_left
        (isHilbertSchmidtNull_soficUnitarySeq_mul S g h)
        (coe_ultrafilter_le_atTop ω hω)
    rw [← map_mul]
    exact mk_eq_mk_of_isHilbertSchmidtNull (X := fun n ↦ S.model n)
      (l := (ω : Filter ℕ)) hnull

@[simp] theorem soficUnitaryHomUltrafilter_apply_coe
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite) (g : G) :
    ((soficUnitaryHomUltrafilter S ω hω g :
        unitary (TracialMatrixQuotient (fun n ↦ S.model n) (ω : Filter ℕ))) :
        TracialMatrixQuotient (fun n ↦ S.model n) (ω : Filter ℕ))
      = tracialMatrixQuotientMk (fun n ↦ S.model n) (ω : Filter ℕ)
          (soficUnitarySeq S g) := rfl

/-- **The ultratrace kills a nontrivial group element's class.**  This is the
printed "`tr_ω(u_g) = 0` for `g ≠ 1`", and it is the sofic fixed-point count
`tendsto_normTrace_modelUnitary_of_ne_one` read along `ω` instead of along
`atTop`. -/
theorem seqUltratrace_soficUnitarySeq_eq_zero
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hpos : ∀ n, 0 < Fintype.card (S.model n)) {g : G} (hg : g ≠ 1) :
    seqUltratrace (fun n ↦ S.model n) ω (soficUnitarySeq S g) = 0 := by
  refine tendsto_nhds_unique
    (tendsto_seqUltratrace (fun n ↦ S.model n) ω (soficUnitarySeq S g)) ?_
  exact Filter.Tendsto.mono_left
    (tendsto_normTrace_modelUnitary_of_ne_one S hpos hg)
    (coe_ultrafilter_le_atTop ω hω)

/-- The same vanishing in the shape `canonicalMaximalTrace_factorsThrough`
consumes: on the bundled functional, at the unitary the representation
assigns to `g`. -/
theorem ultratraceCLM_soficUnitaryHomUltrafilter_eq_zero
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hpos : ∀ n, 0 < Fintype.card (S.model n)) {g : G} (hg : g ≠ 1) :
    ultratraceCLM (fun n ↦ S.model n) ω
        ((soficUnitaryHomUltrafilter S ω hω g :
          unitary (TracialMatrixQuotient (fun n ↦ S.model n)
            (ω : Filter ℕ))) :
          TracialMatrixQuotient (fun n ↦ S.model n) (ω : Filter ℕ)) = 0 := by
  simp only [soficUnitaryHomUltrafilter_apply_coe, ultratraceCLM_apply,
    ultratrace_mk]
  exact seqUltratrace_soficUnitarySeq_eq_zero S ω hω hpos hg

end UltrafilterModel

/-! ## The endpoint -/

/-- The printed sentence of `thm:trace`, as a closed proposition: for a
countable sofic group and *every* free ultrafilter `ω`, the permutation models
extend to a `⋆`-homomorphism `π` out of `C*_max(G)` into the manuscript's
tracial ultraproduct `∏ M_{d_n} / ⊕_{2,ω} M_{d_n}`, the canonical trace is
`tr_ω ∘ π` on the nose, and the canonical trace is therefore a hyperlinear
trace in Shulman's sequential sense.

Three clauses, in the printed order: the extension, the factorization, and the
conclusion.  The first two live in the printed intermediate object; the third
is the printed conclusion, which is sequential and is
`canonicalMaximalTrace_isHyperlinearTrace_of_isSofic`. -/
def SoficCanonicalTraceFactorsThroughTracialUltraproduct : Prop :=
  ∀ (G : Type) [Group G] [Countable G], IsSofic G →
    ∀ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ Filter.cofinite →
      ∃ S : SoficApproximation G, ∃ hpos : ∀ n, 0 < Fintype.card (S.model n),
        letI : ∀ n, Nonempty (S.model n) :=
          fun n ↦ Fintype.card_pos_iff.mp (hpos n)
        ∃ π : MaximalGroupCStar G →⋆ₐ[ℂ]
            TracialMatrixQuotient (fun n ↦ S.model n) (ω : Filter ℕ),
          (∀ g : G, π (maximalGroupCStarGenerator G g)
              = tracialMatrixQuotientMk (fun n ↦ S.model n) (ω : Filter ℕ)
                  (soficUnitarySeq S g)) ∧
            (∀ a : MaximalGroupCStar G,
              ultratrace (fun n ↦ S.model n) ω (π a)
                = canonicalMaximalTrace G a) ∧
            IsHyperlinearTrace
              (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a)

/-- **`thm:trace` with the printed intermediate object.**

The universal property of `C*_max(G)` extends the permutation models to `π`
landing in the manuscript's `ω`-quotient, `τ_G = tr_ω ∘ π` there, and `τ_G` is
a hyperlinear trace.  The factorization is
`canonicalMaximalTrace_factorsThrough`, whose two hypotheses are the printed
normalization `tr_ω 1 = 1` and the printed vanishing `tr_ω(u_g) = 0` for
`g ≠ 1`. -/
theorem canonicalMaximalTrace_factorsThrough_tracialUltraproduct :
    SoficCanonicalTraceFactorsThroughTracialUltraproduct := by
  intro G _ _ hG ω hω
  obtain ⟨S, hpos, -, -⟩ :=
    SoficPermutationTrace.exists_soficApproximation_tendsto_normTrace hG
  letI : ∀ n, Nonempty (S.model n) := fun n ↦
    Fintype.card_pos_iff.mp (hpos n)
  obtain ⟨π, hπgen, hπtrace⟩ :=
    canonicalMaximalTrace_factorsThrough G
      (soficUnitaryHomUltrafilter S ω hω)
      (ultratraceCLM (fun n ↦ S.model n) ω)
      (ultratraceCLM_one (fun n ↦ S.model n) ω)
      (fun g hg ↦
        ultratraceCLM_soficUnitaryHomUltrafilter_eq_zero S ω hω hpos hg)
  refine ⟨S, hpos, π, ?_, ?_,
    canonicalMaximalTrace_isHyperlinearTrace_of_isSofic G hG⟩
  · intro g
    rw [hπgen g]
    rfl
  · intro a
    exact DFunLike.congr_fun hπtrace a

end

end ShulmanTrace
end GroupApproximation
