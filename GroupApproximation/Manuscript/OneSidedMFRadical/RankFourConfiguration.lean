import GroupApproximation.Manuscript.OneSidedMFRadical.RankFourEndpoints

/-!
# The printed rank-four configuration

`non_mf_groups_exist.tex`, proof of `thm:full-defect-ring` at the manuscript's
own ring `R = L_{𝔽₂}(1,2)`, and the section *The binary example*.

The printed proof uses four coordinates: coordinates `1,2,3` carry
`L = EL₃(R)` and coordinate `4` is "for its centralizer".  With `s = s₀`,
`t = t₀` and `e = 1 - s₀t₀ = s₁t₁` the printed data are

* `uᵢ = e₄ᵢ(t-1) eᵢ₄(1) e₄ᵢ(s-1) eᵢ₄(-t)` and `u = u₃u₂u₁`;
* `c = [e₄₁(e), e₁₄(t)] = diag(1,1,1,1+et)`;
* `ucu⁻¹ = e₁₂(e)` and, for `ℓ = e₂₃(1)`, `d = [ucu⁻¹, ℓ] = e₁₃(e)`.

`Leavitt.RankFourCompressors` already carries `u` as a literal word in twelve
elementary transvections, its sparse matrix value, and the conjugation identity
`u γ u⁻¹ = Ψ(γ)` on the embedded core.  What this module adds is the printed
centralizer mark `c`, which is *not* an elementary root at rank four -- every
index pair meets the corner -- and the two calculations the manuscript displays
for it: that `c` centralizes `L`, and that `ucu⁻¹ = e₁₂(e)`.

Everything is proved over an arbitrary ring carrying a binary Leavitt family
and then instantiated at `L_{𝔽₂}(1,2)`; the matrix identities never see the
concrete ring's `RingQuot` instance chain.

Zero-based indices throughout: printed `1,2,3,4` are Lean `0,1,2,3`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankFourEndpoint

open scoped commutatorElement

section Generic

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-! ## The two printed relations on the complementary idempotent -/

/-- **`te = 0`.**  The printed relation `t(1-st) = 0` at `t = t₀`,
`e = s₁t₁`. -/
theorem t0_mul_p1 : L.t0 * L.p1 = 0 := by
  show L.t0 * (L.s1 * L.t1) = 0
  rw [← mul_assoc, L.t0_s1, zero_mul]

/-- **`es = 0`.**  The printed relation `(1-st)s = 0` at `s = s₀`,
`e = s₁t₁`. -/
theorem p1_mul_s0 : L.p1 * L.s0 = 0 := by
  show L.s1 * L.t1 * L.s0 = 0
  rw [mul_assoc, L.t1_s0, mul_zero]

/-! ## The printed centralizer mark -/

/-- **The printed mark `c = [e₄₁(e), e₁₄(t)]`**, zero-based
`⁅e₃₀(e), e₀₃(t)⁆`. -/
def genericMark : RankFour.Ambient A :=
  ⁅elementaryRoot (3 : Fin 4) 0 (by decide) L.p1,
    elementaryRoot (0 : Fin 4) 3 (by decide) L.t0⁆

/-- The mark written out as a four-letter word in elementary transvections. -/
theorem genericMark_eq_word :
    genericMark L =
      elementaryRoot (3 : Fin 4) 0 (by decide) L.p1 *
        elementaryRoot (0 : Fin 4) 3 (by decide) L.t0 *
        elementaryRoot (3 : Fin 4) 0 (by decide) (-L.p1) *
        elementaryRoot (0 : Fin 4) 3 (by decide) (-L.t0) := by
  rw [genericMark, commutatorElement_def, elementaryRoot_neg, elementaryRoot_neg]

/-- **`c = diag(1,1,1,1+et)`.**  The printed evaluation of the mark; it uses
only `te = 0`. -/
theorem genericMark_val :
    ((genericMark L : (Matrix (Fin 4) (Fin 4) A)ˣ) :
        Matrix (Fin 4) (Fin 4) A) =
      1 + Matrix.single (3 : Fin 4) 3 (L.p1 * L.t0) := by
  have hts : L.t0 * L.p1 = 0 := t0_mul_p1 L
  -- `mul_assoc` right-associates, so `t₀ * e` is hidden inside longer words;
  -- the absorbing form is needed alongside the bare relation.
  have hts' : ∀ x : A, L.t0 * (L.p1 * x) = 0 := by
    intro x
    rw [← mul_assoc, hts, zero_mul]
  rw [genericMark_eq_word]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [elementaryRoot, elementaryUnit, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ, Matrix.single_apply, hts, hts', mul_add, add_mul,
      mul_assoc]

/-- **"a diagonal matrix of this shape commutes with every `diag(A,1)`"**, on
the corner generators. -/
theorem genericMark_commutes_coreRoot (i j : Fin 3) (hij : i ≠ j) (a : A) :
    Commute (genericMark L)
      (elementaryRoot (RankFour.coreIndex i) (RankFour.coreIndex j)
        (RankFour.coreIndex_injective.ne hij) a) := by
  apply Subtype.ext
  apply Units.ext
  ext r c
  fin_cases i <;> fin_cases j
  all_goals try simp at hij
  all_goals fin_cases r <;> fin_cases c
  all_goals
    simp [genericMark_val, elementaryRoot, elementaryUnit, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ, Matrix.single_apply,
      RankFour.coreIndex, mul_add, add_mul, mul_assoc]

/-- **"so `c ∈ C_G(L)`"**, on the whole corner. -/
theorem genericMark_commutes_genericCorner :
    ∀ gamma ∈ genericCorner A, Commute (genericMark L) gamma := by
  intro gamma hgamma
  rw [genericCorner] at hgamma
  induction hgamma using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      exact genericMark_commutes_coreRoot L i j hij a
  | one => exact Commute.one_right _
  | mul x y _ _ hx hy => exact hx.mul_right hy
  | inv x _ hx => exact hx.inv_right

/-! ## Moving the mark past the compressor -/

/-- **"the matrix `uc` differs from `u` only in its last column"**, in the form
that avoids `u⁻¹`: `uc = e₁₂(e)u`.  It uses `t³e = 0` through `te = 0`, the
idempotence `e² = e`, and `es = 0`. -/
theorem compressor_mul_genericMark :
    RankFour.compressor L * genericMark L =
      elementaryRoot (0 : Fin 4) 1 (by decide) L.p1 * RankFour.compressor L := by
  have hts : L.t0 * L.p1 = 0 := t0_mul_p1 L
  have hes : L.p1 * L.s0 = 0 := p1_mul_s0 L
  -- `mul_assoc` right-associates every product, so `t₀ * e` never appears as a
  -- subterm; the absorbing form is what the entry calculation actually needs.
  have hts' : ∀ x : A, L.t0 * (L.p1 * x) = 0 := by
    intro x
    rw [← mul_assoc, hts, zero_mul]
  apply Subtype.ext
  apply Units.ext
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [RankFour.compressor_val, genericMark_val, RankFour.compressorMatrix,
      elementaryRoot, elementaryUnit, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ, Matrix.single_apply, hes, hts', mul_add, add_mul,
      mul_assoc]

/-- **`ucu⁻¹ = e₁₂(e)`**, zero-based `e₀₁(e)`. -/
theorem compressor_conj_genericMark :
    RankFour.compressor L * genericMark L * (RankFour.compressor L)⁻¹ =
      elementaryRoot (0 : Fin 4) 1 (by decide) L.p1 := by
  rw [compressor_mul_genericMark]
  group

/-- **`d = [ucu⁻¹, ℓ] = e₁₃(e)`**, zero-based `e₀₂(e)`, for the printed
`ℓ = e₂₃(1)`. -/
theorem genericDefect_commutator :
    ⁅RankFour.compressor L * genericMark L * (RankFour.compressor L)⁻¹,
        elementaryRoot (1 : Fin 4) 2 (by decide) 1⁆ =
      elementaryRoot (0 : Fin 4) 2 (by decide) L.p1 := by
  rw [compressor_conj_genericMark]
  simpa using
    elementaryRoot_commutator (R := A) (0 : Fin 4) 1 2
      (by decide) (by decide) (by decide) L.p1 1

/-- **`uLu⁻¹ ≤ L`.**  The conjugation identity of `Leavitt.RankFourCompressors`
plus the identification of the corner with the range of the core embedding. -/
theorem compressor_compresses_genericCorner :
    ∀ gamma ∈ genericCorner A,
      RankFour.compressor L * gamma * (RankFour.compressor L)⁻¹ ∈
        genericCorner A := by
  intro gamma hgamma
  obtain ⟨g, rfl⟩ := genericCorner_le_range hgamma
  rw [RankFour.compressor_conjugation]
  exact coreEmbedding_mem_genericCorner _

end Generic

/-! ## The configuration at the manuscript's ring -/

theorem u_eq_compressor : u = RankFour.compressor leavittFamily := rfl

theorem c_eq_genericMark : c = genericMark leavittFamily := rfl

/-- **`c = diag(1,1,1,1+et)`** at the manuscript's ring. -/
theorem c_val :
    ((c : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) =
      1 + Matrix.single (3 : Fin 4) 3 (q * leavittFamily.t0) :=
  genericMark_val leavittFamily

/-- **The printed mark centralizes the printed corner.** -/
theorem c_commutes_corner : ∀ gamma ∈ corner, Commute c gamma := by
  rw [c_eq_genericMark, corner_eq_genericCorner]
  exact genericMark_commutes_genericCorner leavittFamily

/-- **`uLu⁻¹ ≤ L`** at the manuscript's ring. -/
theorem u_compresses_corner : ∀ gamma ∈ corner, u * gamma * u⁻¹ ∈ corner := by
  rw [u_eq_compressor, corner_eq_genericCorner]
  exact compressor_compresses_genericCorner leavittFamily

/-- **`ucu⁻¹ = e₀₁(q)`** at the manuscript's ring. -/
theorem u_conj_c :
    u * c * u⁻¹ = elementaryRoot (0 : Fin 4) 1 (by decide) q :=
  compressor_conj_genericMark leavittFamily

/-- **The exact commutator identity of the printed proof.** -/
theorem u_c_commutator_ell : ⁅u * c * u⁻¹, ell⁆ = defect :=
  genericDefect_commutator leavittFamily

/-- **The printed rank-four configuration, closed.** -/
theorem printedDefectConfiguration : PrintedDefectConfiguration :=
  ⟨corner_hasKazhdanPropertyT, c_commutes_corner, u_compresses_corner,
    u_c_commutator_ell⟩

/-- **The printed compression step, exactly and without hypotheses.**  The
transparent definitions above are the manuscript's literal elements
`c = [e₄₁(e), e₁₄(t)]`, `ℓ = e₂₃(1)`, `d = e₁₃(e)`, and the comb compressor
`u = u₃u₂u₁`.  The four conjuncts below are precisely the four printed
assertions: centrality of `c` relative to the canonical upper-left `EL₃`, the
displayed commutator calculation, nontriviality of `d`, and normal generation
of `H`.  No simplicity input is consumed: normal generation is the
independently closed elementary-root theorem. -/
def PropositionDefect : Prop :=
  (∀ gamma ∈ corner, Commute c gamma) ∧
    ⁅u * c * u⁻¹, ell⁆ = defect ∧
    defect ≠ 1 ∧
    Subgroup.normalClosure ({defect} : Set H) = ⊤

theorem manuscriptPropositionDefect : PropositionDefect :=
  ⟨c_commutes_corner, u_c_commutator_ell,
    defect_ne_one, normalClosure_defect_eq_top⟩

/-- **`Rad_MF(H) = H` at rank four**, in the basis-free reading. -/
theorem rankFour_actualCoronaMFResidual_eq_top :
    actualCoronaMFResidual H = ⊤ :=
  residual_eq_top_of_configuration printedDefectConfiguration

/-! ## Strictness of the compression

`cor:one-sided-ring-maximal` needs more than `uLu⁻¹ ≤ L`: it needs the
inclusion to be proper.  The printed argument is that "every off-diagonal entry
of a matrix in `uLu⁻¹` has the form `sat`, and `e(sat) = 0` while `e·1 = e ≠ 0`,
so `e₁₂(1) ∈ L ∖ uLu⁻¹`."  Here the same conclusion is reached from the single
relation `t₁(s₀at₀)s₁ = 0 ≠ 1`. -/

/-- **`t₁(s₀at₀)s₁ = 0 ≠ 1 = t₁·1·s₁`**, in the form the printed strictness
argument uses it: no element of the corner `s₀Rt₀` is the identity of `R`. -/
theorem printed_s0_mul_t0_ne_one (a : R) :
    leavittFamily.s0 * a * leavittFamily.t0 ≠ 1 := by
  intro h
  have hone : leavittFamily.t1 * (leavittFamily.s0 * a * leavittFamily.t0) *
      leavittFamily.s1 = 1 := by
    rw [h, mul_one, leavittFamily.t1_s1]
  have hsplit : leavittFamily.t1 * (leavittFamily.s0 * a * leavittFamily.t0) *
      leavittFamily.s1 =
      leavittFamily.t1 * leavittFamily.s0 * a *
        (leavittFamily.t0 * leavittFamily.s1) := by
    noncomm_ring
  rw [hsplit, leavittFamily.t1_s0, leavittFamily.t0_s1, zero_mul, zero_mul]
    at hone
  exact zero_ne_one hone

/-- The printed `ℓ = e₂₃(1)` is the core embedding of the corresponding
`EL₃`-transvection. -/
theorem coreEmbedding_coreTransvection_one_two :
    RankFour.coreEmbedding
      (RankFour.coreTransvection (A := R) 1 2 (by decide) 1) = ell := by
  rw [RankFour.coreEmbedding_coreTransvection]
  exact ell_eq_cornerRoot.symm

/-- **"so `e₁₂(1) ∈ L ∖ uLu⁻¹`"**, the half that needs proving.

If `ell` were `uγu⁻¹` with `γ ∈ L`, then writing `γ = coreEmbedding g` and
conjugating turns the printed `e₂₃(1)` into `Ψ(g)`; injectivity of the core
embedding makes that an identity of `3 × 3` elements, and its `(1,2)` entry
says `1 = s₀·g₁₂·t₀`, which `printed_s0_mul_t0_ne_one` refutes. -/
theorem ell_not_mem_u_conj_corner :
    ell ∉ corner.map (MulAut.conj u).toMonoidHom := by
  rintro ⟨gamma, hgamma, hconj⟩
  obtain ⟨g, rfl⟩ := corner_le_coreEmbedding_range hgamma
  have hH : u * RankFour.coreEmbedding g * u⁻¹ = ell := by
    simpa using hconj
  rw [u_eq_compressor, RankFour.compressor_conjugation] at hH
  have hg : RankFour.compressionEnd leavittFamily g =
      RankFour.coreTransvection (A := R) 1 2 (by decide) 1 :=
    RankFour.coreEmbedding_injective
      (hH.trans coreEmbedding_coreTransvection_one_two.symm)
  have hentry := congrArg (fun z : RankFour.Core R ↦
    ((z : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) 1 2) hg
  refine printed_s0_mul_t0_ne_one
    (((g : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) 1 2) ?_
  simpa [RankFour.compressionEnd, LeavittFamily.elementaryCompressionEnd,
    LeavittFamily.matrixCompressionHom_val,
    LeavittFamily.matrixCompression_apply, RankFour.coreTransvection,
    elementaryUnit, Matrix.single_apply, Matrix.one_apply] using hentry

/-- **`uLu⁻¹ ≤ L`**, in the `Subgroup.map` spelling `prop:max-infinite`
consumes. -/
theorem u_conj_corner_le :
    corner.map (MulAut.conj u).toMonoidHom ≤ corner := by
  rintro x ⟨gamma, hgamma, rfl⟩
  simpa using u_compresses_corner gamma hgamma

/-- **"The compression is strict"**, `uLu⁻¹ ⊊ L`. -/
theorem u_conj_corner_lt :
    corner.map (MulAut.conj u).toMonoidHom < corner :=
  lt_of_le_of_ne u_conj_corner_le (by
    intro h
    exact ell_not_mem_u_conj_corner (by rw [h]; exact ell_mem_corner))

end RankFourEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
