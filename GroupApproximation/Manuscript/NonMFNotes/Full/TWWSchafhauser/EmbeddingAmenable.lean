import GroupApproximation.Analysis.TikuisisWhiteWinterCore
import GroupApproximation.Analysis.UCPContractiveMatrix
import GroupApproximation.Analysis.GoldbringHartRoute

/-!
# An amenable trace model as a ucp lift and a ⋆-homomorphism into `Q^ω`

Lane TWWSchafhauser-3b (work order WO-TWWCore-3, piece 3b).  The source is
C. Schafhauser, *A new proof of the Tikuisis--White--Winter theorem*, J. reine
angew. Math. 759 (2020), §2--3, together with Brown--Ozawa, Ch. 6.  The one
sentence used there is this: an amenable trace `τ` gives a unital ⋆-homomorphism
`θ : A → Q^ω = ∏_ω M_{k(n)}` with `tr_ω ∘ θ = τ`, and `θ` has a ucp lift
`A → ℓ∞(M_{k(n)})` given by the model maps.

Fix an amenable trace model `M : Quasidiagonal.AmenableTraceModel τ`.  Its maps
are unital completely positive maps `φ_n : A → M_{k(n)}` that are
asymptotically multiplicative in `‖·‖₂` and whose normalized traces converge to
`τ`.

* `tailSpace M N` and `tailSeq M N a` shift past index `N` and assemble the bounded
  sequence `(φ_{n+N} a)_n`.  It is bounded by `‖a‖` (`Quasidiagonal.ucp_norm_le`).
* `tailLift M N : A →ₗ[ℂ] ℓ∞(M_{k(n+N)})` is the ucp lift.  Its coordinates are the
  ucp maps `φ_{n+N}` (`tailLift_apply`), and it is contractive (`norm_tailLift_le`).
* `tailHom M N l hl : A →⋆ₐ[ℂ] TracialMatrixQuotient (tailSpace M N) l` is the
  composite of the lift with the quotient map, for any filter `l ≤ atTop`.  It
  preserves `⋆` because `Quasidiagonal.ucp_map_star` does.  It is multiplicative
  because the defect `tailSeq (ab) − tailSeq a · tailSeq b` is `‖·‖₂`-null.
* `ultratraceCLM_tailHom`: along an ultrafilter `ω ≤ atTop`, `tr_ω ∘ tailHom = τ`.
* `exists_tail_card_pos`: when `τ 1 = 1` the models are eventually nonempty.  The
  normalization is necessary: `τ = 0` is amenable (empty models), but
  `tr_ω 1 = 1`.

The same content exists, without the lift, in the foreign never-wired modules
`Manuscript/NonMF/TWWLanes/AmenableUltraHom/*`.  It is re-proved here so that no
foreign orphan gets wired.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Filter
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

variable {A : Type u} [CStarAlgebra A] {τ : A → ℂ}
variable (M : Quasidiagonal.AmenableTraceModel τ)

/-- **A normalized amenable trace has eventually nonempty models.**  An empty model
has normalized trace `0`, but the trace clause at `1` puts it within `1` of
`τ 1 = 1`. -/
theorem exists_tail_card_pos (hone : τ 1 = 1) :
    ∃ K : ℕ, ∀ n, K ≤ n → 0 < Fintype.card (M.space n) := by
  have hlt : ∀ᶠ n in atTop,
      ‖τ 1 - normTrace (M.space n) (M.map n 1)‖ < 1 :=
    (M.tendsto_trace 1).eventually_lt_const one_pos
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hlt
  refine ⟨K, fun n hn => ?_⟩
  have hn' := hK n hn
  by_contra hcard
  have hzero : Fintype.card (M.space n) = 0 := by omega
  have hnt : normTrace (M.space n) (M.map n 1) = 0 := by
    show Matrix.trace (M.map n 1)
      / ((Fintype.card (M.space n) : ℕ) : ℂ) = 0
    rw [hzero, Nat.cast_zero, div_zero]
  rw [hnt, hone, sub_zero, norm_one] at hn'
  exact lt_irrefl 1 hn'

variable (N : ℕ)

/-- The models shifted past index `N`. -/
abbrev tailSpace : ℕ → FiniteModel := fun n => M.space (n + N)

/-- The bounded matrix sequence `(φ_{n+N} a)_n`.  It is bounded by `‖a‖` because each
`φ_n` is unital and completely positive. -/
def tailSeq (a : A) : TracialUltraproduct.ModelBoundedSequence (tailSpace M N) :=
  ⟨fun n => M.map (n + N) a, memℓp_infty ⟨‖a‖, by
    rintro _ ⟨n, rfl⟩
    exact Quasidiagonal.ucp_norm_le (M.map (n + N)) (M.map_one (n + N))
      (M.completelyPositive (n + N)) a⟩⟩

theorem tailSeq_apply (a : A) (n : ℕ) : tailSeq M N a n = M.map (n + N) a :=
  rfl

theorem tailSeq_zero : tailSeq M N 0 = 0 := by
  refine lp.ext (funext fun n => ?_)
  change M.map (n + N) 0 = 0
  exact map_zero (M.map (n + N))

theorem tailSeq_add (a b : A) :
    tailSeq M N (a + b) = tailSeq M N a + tailSeq M N b := by
  refine lp.ext (funext fun n => ?_)
  change M.map (n + N) (a + b) = M.map (n + N) a + M.map (n + N) b
  exact map_add (M.map (n + N)) a b

theorem tailSeq_smul (c : ℂ) (a : A) :
    tailSeq M N (c • a) = c • tailSeq M N a := by
  refine lp.ext (funext fun n => ?_)
  change M.map (n + N) (c • a) = c • M.map (n + N) a
  exact map_smul (M.map (n + N)) c a

theorem tailSeq_one : tailSeq M N 1 = 1 := by
  refine lp.ext (funext fun n => ?_)
  change M.map (n + N) 1 = 1
  exact M.map_one (n + N)

theorem tailSeq_star (a : A) :
    tailSeq M N (star a) = star (tailSeq M N a) := by
  refine lp.ext (funext fun n => ?_)
  change M.map (n + N) (star a) = star (M.map (n + N) a)
  rw [Matrix.star_eq_conjTranspose]
  exact Quasidiagonal.ucp_map_star (M.map (n + N)) (M.map_one (n + N))
    (M.completelyPositive (n + N)) a

/-- **The ucp lift `A → ℓ∞(M_{k(n+N)})`** (Schafhauser 2020, §3).  Its coordinates are
the unital completely positive model maps. -/
def tailLift : A →ₗ[ℂ] TracialUltraproduct.ModelBoundedSequence (tailSpace M N) where
  toFun := tailSeq M N
  map_add' := tailSeq_add M N
  map_smul' c a := tailSeq_smul M N c a

theorem tailLift_apply (a : A) (n : ℕ) : tailLift M N a n = M.map (n + N) a :=
  rfl

/-- The coordinates of the lift are unital. -/
theorem tailLift_map_one (n : ℕ) : M.map (n + N) 1 = 1 :=
  M.map_one (n + N)

/-- The coordinates of the lift are completely positive. -/
theorem tailLift_completelyPositive (n : ℕ) :
    Quasidiagonal.IsCompletelyPositiveOnMatrices (tailSpace M N n) ⇑(M.map (n + N)) :=
  M.completelyPositive (n + N)

/-- The lift is contractive. -/
theorem norm_tailLift_le (a : A) : ‖tailLift M N a‖ ≤ ‖a‖ :=
  lp.norm_le_of_forall_le (norm_nonneg a) fun n =>
    Quasidiagonal.ucp_norm_le (M.map (n + N)) (M.map_one (n + N))
      (M.completelyPositive (n + N)) a

/-- The shifted multiplicative defect is `‖·‖₂`-null. -/
theorem tendsto_hsNorm_tailSeq_mul (a b : A) :
    Tendsto (fun n => hsNorm (tailSpace M N n)
      (M.map (n + N) (a * b) - M.map (n + N) a * M.map (n + N) b))
      atTop (nhds 0) :=
  (tendsto_add_atTop_iff_nat (f := fun n =>
      hsNorm (M.space n) (M.map n (a * b) - M.map n a * M.map n b)) N).mpr
    (M.tendsto_mul_hs a b)

section Quotient

variable [∀ n, Nonempty (tailSpace M N n)] (l : Filter ℕ)

/-- The lift followed by the quotient map onto the tracial matrix quotient. -/
def tailQuotientLinear : A →ₗ[ℂ] TracialUltraproduct.TracialMatrixQuotient (tailSpace M N) l where
  toFun a := TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l (tailSeq M N a)
  map_add' a b := by
    show TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l (tailSeq M N (a + b))
      = TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l (tailSeq M N a)
        + TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l (tailSeq M N b)
    rw [tailSeq_add, map_add]
  map_smul' c a := by
    show TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l (tailSeq M N (c • a))
      = c • TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l (tailSeq M N a)
    rw [tailSeq_smul]
    exact map_smul (TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l) c
      (tailSeq M N a)

theorem tailQuotientLinear_apply (a : A) :
    tailQuotientLinear M N l a
      = TracialUltraproduct.tracialMatrixQuotientMk (tailSpace M N) l (tailSeq M N a) :=
  rfl

theorem tailQuotientLinear_one : tailQuotientLinear M N l 1 = 1 := by
  rw [tailQuotientLinear_apply, tailSeq_one]
  exact map_one (TracialUltraproduct.tracialMatrixQuotientMk (tailSpace M N) l)

theorem tailQuotientLinear_mul (hl : l ≤ atTop) (a b : A) :
    tailQuotientLinear M N l (a * b)
      = tailQuotientLinear M N l a * tailQuotientLinear M N l b := by
  rw [tailQuotientLinear_apply, tailQuotientLinear_apply, tailQuotientLinear_apply]
  have hzero : TracialUltraproduct.tracialMatrixQuotientMk (tailSpace M N) l
      (tailSeq M N (a * b) - tailSeq M N a * tailSeq M N b) = 0 :=
    (TracialUltraproduct.tracialMatrixQuotientMk_eq_zero_iff (tailSpace M N) l _).mpr
      ((tendsto_hsNorm_tailSeq_mul M N a b).mono_left hl)
  rw [map_sub, map_mul, sub_eq_zero] at hzero
  exact hzero

/-- **The model as a unital ⋆-homomorphism into the tracial matrix quotient**
(Schafhauser 2020, §3), along any filter finer than `atTop`. -/
def tailHom (hl : l ≤ atTop) :
    A →⋆ₐ[ℂ] TracialUltraproduct.TracialMatrixQuotient (tailSpace M N) l where
  toAlgHom := AlgHom.ofLinearMap (tailQuotientLinear M N l)
    (tailQuotientLinear_one M N l) (tailQuotientLinear_mul M N l hl)
  map_star' a := by
    show TracialUltraproduct.tracialMatrixQuotientMk (tailSpace M N) l (tailSeq M N (star a))
      = star (TracialUltraproduct.tracialMatrixQuotientMk (tailSpace M N) l (tailSeq M N a))
    rw [tailSeq_star]
    exact map_star (TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l) _

/-- `tailHom` is the quotient map applied to the ucp lift. -/
theorem tailHom_apply (hl : l ≤ atTop) (a : A) :
    tailHom M N l hl a
      = TracialUltraproduct.tracialMatrixQuotientMk (tailSpace M N) l (tailLift M N a) :=
  rfl

end Quotient

/-- **Trace preservation.**  Along an ultrafilter finer than `atTop`, the ultratrace
of `tailHom` recovers `τ`. -/
theorem ultratraceCLM_tailHom [∀ n, Nonempty (tailSpace M N n)] (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ atTop) (a : A) :
    TracialUltraproduct.ultratraceCLM (tailSpace M N) ω
      (tailHom M N (ω : Filter ℕ) hω a) = τ a := by
  have h0 : Tendsto (fun n => normTrace (M.space n) (M.map n a)) atTop
      (nhds (τ a)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr
      ((M.tendsto_trace a).congr fun n => norm_sub_rev (τ a) _)
  have hshift : Tendsto (fun n => normTrace (M.space (n + N)) (M.map (n + N) a))
      (ω : Filter ℕ) (nhds (τ a)) :=
    ((tendsto_add_atTop_iff_nat
      (f := fun n => normTrace (M.space n) (M.map n a)) N).mpr h0).mono_left hω
  show TracialUltraproduct.ultratrace (tailSpace M N) ω
      (TracialUltraproduct.tracialMatrixQuotientMk (tailSpace M N) (ω : Filter ℕ)
        (tailSeq M N a)) = τ a
  rw [TracialUltraproduct.ultratrace_mk]
  show UltrafilterLimit.ulim ω
      (fun n => normTrace (M.space (n + N)) (M.map (n + N) a)) = τ a
  exact UltrafilterLimit.ulim_eq hshift

end

end GroupApproximation.Full.TWWSchafhauser
