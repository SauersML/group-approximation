import GroupApproximation.Sofic.ManuscriptKazhdanTransport
import GroupApproximation.Sofic.MarkedCompressionRootCapture
import GroupApproximation.Sofic.UltraproductKazhdanTransport

/-!
# INT.03 and INT.04: the rigidity claims through the printed transport

The introduction's rigidity paragraph (`p:abstract-mechanism`) says

> rigidity: if `t Γ t⁻¹ ⊆ Γ` then conjugation by `t` preserves the
> Hilbert--Schmidt asymptotic commutant of `Γ`,

and then, in `E`, that this forces the commutator `u` to converge to `1` in
normalized Hilbert--Schmidt norm.  The proof ledger records both rows as routed
through the **finite-stage** proof: `INT.03` reads
"the Lean route is Appendix B, not the printed §3 ultraproduct proof", and
`INT.04` reads "route via Appendix B".

**That appendix is no longer printed.**  Commit `3a45fa60` ("Editorial pass:
rewrite orbit collapse, cut what nothing uses") deleted the finite-stage
transport appendix and the remark announcing it, on the ground that the
ultraproduct reading of the collapse step had become its only consumer.  The
manuscript now proves `\ref{thm:kazhdan-transport}` once, inside
`\ref{sec:transport}`.  The Lean chain below is unaffected -- it was never a
transcription of that appendix, and the two routes remain interchangeable --
but "Appendix B" in the ledger rows above names a passage the reader will not
find, and is kept only because those rows are quoted verbatim.

That is accurate.  `LiteralNonMFEndpoint.kazhdanPinning` unfolds to
`KazhdanCompressionCore.compressionDefects_hsTrivial`, which unfolds to
`KazhdanCompressorCorner.compressionDefect_hsDistSq_vanishing`, and the *only*
step of that chain which is transport rather than operator-norm bookkeeping is

  `KazhdanCompressorCorner.transportedRoot_displacement_hsDistSq_vanishing`,

proved with an almost-fixed spectral corner, `root_capture_vanishing` and the
reversal estimate -- Appendix B, with explicit constants `ε/6`, `ε/48` and
`θ = (c₀+1)/2`.  Meanwhile `KazhdanAsymptoticCommutant.manuscriptKazhdanTransport`,
which *is* derived by the printed §3 ultraproduct proof
(`ultraproductKazhdanTransport`), has no mathematical consumer anywhere in the
development: it is only re-exported and audited.

## What this file supplies

The lemmas that make the printed conclusion and the Appendix-B lemma the *same
statement*, so that the route can be exchanged without touching any endpoint.

* `hsDistSq_conj_eq_hsNormSq_commutator` -- the printed "by unitary invariance
  of the normalized Hilbert--Schmidt norm": the displacement `V A V* − A` and
  the commutator `AV − VA` have the same normalized Hilbert--Schmidt norm.  This
  is the exact identity that turns the transport conclusion, which is stated as
  a commutator, into the displacement the corner chain consumes.
* `centralRoot_commutator_opNormVanishing` and
  `centralRoot_commutator_hsNormSq_vanishing` -- the transport's *hypothesis* at
  the root element: because `c` centralizes `ι(Γ)`, the microstate `V_c`
  asymptotically commutes with `V_{ι γ}`, in operator norm and hence in
  normalized Hilbert--Schmidt norm.  This is the printed "Since `c` centralizes
  `ι(Γ)`, the sequence `(W_{c,n})` centralizes `(W_{ι(γ),n})` asymptotically in
  operator norm, hence in normalized Hilbert--Schmidt norm" of
  `\label{thm:sign-criterion}`.
* `transportedRoot_displacement_of_hsCommutator` -- the drop-in: from the
  printed transport conclusion at `x_n = V_c` and `s = t`, the statement of
  `transportedRoot_displacement_hsDistSq_vanishing` follows.  The lamp
  microstate `lampMatrix B C n` is `V_t V_c V_t*`, which is exactly the
  transported vector `Ad U_n(t) x_n` of the printed conclusion, so no object is
  substituted.

and then the rewired lemma itself:

* `transportedRoot_displacement_ultraproduct` -- the Appendix-B displacement
  lemma, character for character, proved by one application of
  `manuscriptKazhdanTransport` at `s = t` and `x_n = V_c`.  No spectral corner,
  no reversal estimate, no explicit constant.

The coordinate bridge in between is `hsNormSq_matrixReindex`: the transport is
stated over `naturalFiniteModel (d n)` while an `OpAlmostRepresentation` carries
an arbitrary `FiniteModel` at each stage, and
`Analysis/NaturalMatrixCoordinateEquiv.lean` already supplies the reindexing and
its *operator*-norm invariance but not its normalized Hilbert--Schmidt
invariance.

## What is not here

The flip itself.  `KazhdanCompressorCorner.compressionDefect_hsDistSq_vanishing`
calls the Appendix-B lemma by name, and it lives in
`Sofic/MarkedCompressionRootCapture.lean`, which this file imports -- so making
that call site read `transportedRoot_displacement_ultraproduct` here would be an
import cycle.  Completing rows `INT.03` and `INT.04` is therefore one edit *in
that file*, replacing

  `transportedRoot_displacement_hsDistSq_vanishing B C gamma`

by this declaration, once the two files are ordered the other way round (or once
the operator-norm bookkeeping of `compressionDefect_hsDistSq_vanishing` is moved
below both).  Nothing mathematical remains.
-/

namespace GroupApproximation
namespace UltraproductRigidityRoute

open Matrix KazhdanCornerMatrices KazhdanCompressorCorner
open scoped Matrix.Norms.L2Operator commutatorElement

noncomputable section

universe u

/-! ## Two scalar helpers -/

/-- Square roots reflect order on nonnegatives.  Used to move between the
printed `‖·‖ → 0` and the squared quantities the corner chain carries. -/
theorem le_of_sqrt_le_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : Real.sqrt a ≤ Real.sqrt b) : a ≤ b := by
  have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have h2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-! ## The printed unitary-invariance bridge -/

/-- **Unitary invariance of the normalized Hilbert--Schmidt norm, in the form
the two routes need to be compared.**

The displacement of the adjoint action and the commutator have the same
normalized Hilbert--Schmidt norm:

`‖V A V* − A‖₂ = ‖A V − V A‖₂`,

because `A V − V A = (A − V A V*) V` and right multiplication by a unitary is a
`‖·‖₂`-isometry.  The printed proof of `\ref{thm:kazhdan-transport}` states its
conclusion as a commutator; the corner chain of the finite-stage route (Lean
only, since `3a45fa60` cut the appendix that printed it) states its as a
displacement; this is the identity that makes them one statement. -/
theorem hsDistSq_conj_eq_hsNormSq_commutator (Y : FiniteModel)
    {V : Matrix Y Y ℂ} (hV : V ∈ Matrix.unitaryGroup Y ℂ) (A : Matrix Y Y ℂ) :
    hsDistSq Y (V * A * Vᴴ) A = hsNormSq Y (A * V - V * A) := by
  have hVstarV : Vᴴ * V = 1 := Unitary.star_mul_self_of_mem hV
  have hfactor : A * V - V * A = (A - V * A * Vᴴ) * V := by
    noncomm_ring [hVstarV]
  rw [hfactor, hsNormSq_mul_right Y hV]
  have hneg : hsNormSq Y (-(A - V * A * Vᴴ)) = hsNormSq Y (A - V * A * Vᴴ) :=
    hsNormSq_neg Y _
  show hsNormSq Y (V * A * Vᴴ - A) = hsNormSq Y (A - V * A * Vᴴ)
  rw [← hneg]
  congr 1
  abel

/-! ## The transport hypothesis at the root element -/

section Core

variable {Γ : Type} [Group Γ] {E : Type u} [Group E]

/-- **The root microstate asymptotically commutes with the Kazhdan image, in
operator norm.**  This is the printed sentence "Since `c` centralizes `ι(Γ)`,
the sequence `(W_{c,n})` centralizes `(W_{ι(γ),n})` asymptotically in operator
norm", and it is the hypothesis `thm:kazhdan-transport` is applied with.

Only `comm_c` and asymptotic multiplicativity are used: the commutator of the
two microstates is the difference of the two multiplicative defects at
`(c, ι γ)` and `(ι γ, c)`, whose group products agree because `c` and `ι γ`
commute. -/
theorem centralRoot_commutator_opNormVanishing
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E) (γ : Γ) :
    OpNormVanishing B (fun n ↦
      (B.map n C.c : Matrix (B.model n) (B.model n) ℂ) * B.map n (C.iota γ)
        - (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
          * B.map n C.c) := by
  have h1 := (multiplicativeDefect_vanishing B C.c (C.iota γ)).neg
  have h2 := multiplicativeDefect_vanishing B (C.iota γ) C.c
  have hcomm : C.c * C.iota γ = C.iota γ * C.c := C.comm_c γ
  refine (h1.add h2).congr fun n ↦ ?_
  show -((B.map n (C.c * C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
        - (B.map n C.c : Matrix (B.model n) (B.model n) ℂ) * B.map n (C.iota γ))
      + ((B.map n (C.iota γ * C.c) : Matrix (B.model n) (B.model n) ℂ)
        - (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) * B.map n C.c)
      = _
  rw [hcomm]
  abel

/-- **The same, in normalized Hilbert--Schmidt norm.**  The printed step "hence
in normalized Hilbert--Schmidt norm" is the inequality `‖·‖₂ ≤ ‖·‖`, which needs
only that the coordinate models are nonempty.

This is exactly the hypothesis `_hx` of
`KazhdanAsymptoticCommutant.manuscriptKazhdanTransport`, at the root element
`x_n = V_c`. -/
theorem centralRoot_commutator_hsNormSq_vanishing
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E) (γ : Γ) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      Real.sqrt (hsNormSq (B.model n)
        ((B.map n C.c : Matrix (B.model n) (B.model n) ℂ) * B.map n (C.iota γ)
          - (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
            * B.map n C.c)) ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := centralRoot_commutator_opNormVanishing B C γ ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  set M : Matrix (B.model n) (B.model n) ℂ :=
    (B.map n C.c : Matrix (B.model n) (B.model n) ℂ) * B.map n (C.iota γ)
      - (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) * B.map n C.c
  have hop : ‖M‖ ≤ ε := hN n hn
  have hle : hsNormSq (B.model n) M ≤ ‖M‖ * ‖M‖ :=
    hsNormSq_le_mul_self_l2_opNorm (B.model n) (B.modelNonempty n) M
  have hsq : Real.sqrt (hsNormSq (B.model n) M) ≤ Real.sqrt (‖M‖ * ‖M‖) :=
    Real.sqrt_le_sqrt hle
  rw [Real.sqrt_mul_self (norm_nonneg M)] at hsq
  exact hsq.trans hop

/-! ## The drop-in for the Appendix-B displacement lemma -/

/-- **The printed transport conclusion is the Appendix-B displacement
statement.**

The lamp microstate is `lampMatrix B C n = V_t V_c V_t*`, which is the
transported vector `Ad U_n(t) x_n` of the printed conclusion at `x_n = V_c` and
`s = t`.  Given that conclusion -- the commutator of the transported vector with
`V_{ι γ}` vanishing in normalized Hilbert--Schmidt norm -- the displacement
statement of `KazhdanCompressorCorner.transportedRoot_displacement_hsDistSq_vanishing`
follows, by unitary invariance and nothing else.

So substituting this for the Appendix-B lemma inside
`compressionDefect_hsDistSq_vanishing` exchanges the route without changing any
statement in the chain, which is what rows `INT.03` and `INT.04` ask for. -/
theorem transportedRoot_displacement_of_hsCommutator
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E) (γ : Γ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      Real.sqrt (hsNormSq (B.model n)
        (lampMatrix B C n
            * (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
          - (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
            * lampMatrix B C n)) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      hsDistSq (B.model n)
        ((B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) *
          lampMatrix B C n *
          (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ)
        (lampMatrix B C n) ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := h (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [hsDistSq_conj_eq_hsNormSq_commutator (B.model n)
    (B.map n (C.iota γ)).2 (lampMatrix B C n)]
  exact le_of_sqrt_le_sqrt (hsNormSq_nonneg _ _) hε.le (hN n hn)

end Core

/-! ## The coordinate bridge

`manuscriptKazhdanTransport` is stated over `naturalFiniteModel (d n)`, while an
`OpAlmostRepresentation` carries an arbitrary `FiniteModel` at each stage.
`Analysis/NaturalMatrixCoordinateEquiv.lean` supplies the reindexing and its
operator-norm invariance; what it does not supply, and what the transfer needs,
is invariance of the *normalized Hilbert--Schmidt* norm.  That is the one lemma
here: reindexing permutes the double sum of squared entries and leaves the
cardinality alone. -/

section Reindex

variable {Y : FiniteModel} {d : ℕ}

@[simp] theorem matrixReindex_apply (e : Y ≃ Fin d) (A : Matrix Y Y ℂ) (i j : Fin d) :
    (matrixReindexStarAlgEquiv e A) i j = A (e.symm i) (e.symm j) := rfl

theorem matrixReindex_conjTranspose (e : Y ≃ Fin d) (A : Matrix Y Y ℂ) :
    matrixReindexStarAlgEquiv e Aᴴ = (matrixReindexStarAlgEquiv e A)ᴴ := by
  rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, map_star]

/-- **Reindexing is an isometry for the normalized Hilbert--Schmidt norm.** -/
theorem hsNormSq_matrixReindex (e : Y ≃ Fin d) (A : Matrix Y Y ℂ) :
    hsNormSq (naturalFiniteModel d) (matrixReindexStarAlgEquiv e A)
      = hsNormSq Y A := by
  have hcard : Fintype.card Y = d :=
    (Fintype.card_congr e).trans (Fintype.card_fin d)
  have hnum : ∑ i : Fin d, ∑ j : Fin d,
        Complex.normSq ((matrixReindexStarAlgEquiv e A) i j)
      = ∑ i : Y, ∑ j : Y, Complex.normSq (A i j) := by
    calc ∑ i : Fin d, ∑ j : Fin d,
          Complex.normSq ((matrixReindexStarAlgEquiv e A) i j)
        = ∑ i : Fin d, ∑ j : Fin d,
            Complex.normSq (A (e.symm i) (e.symm j)) := by
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
          rw [matrixReindex_apply]
      _ = ∑ i : Fin d, ∑ j : Y, Complex.normSq (A (e.symm i) j) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          exact Equiv.sum_comp e.symm (fun j ↦ Complex.normSq (A (e.symm i) j))
      _ = ∑ i : Y, ∑ j : Y, Complex.normSq (A i j) :=
          Equiv.sum_comp e.symm (fun i ↦ ∑ j : Y, Complex.normSq (A i j))
  show (∑ i : Fin d, ∑ j : Fin d,
        Complex.normSq ((matrixReindexStarAlgEquiv e A) i j))
        / (Fintype.card (naturalFiniteModel d) : ℝ)
      = (∑ i : Y, ∑ j : Y, Complex.normSq (A i j)) / (Fintype.card Y : ℝ)
  rw [hnum, card_naturalFiniteModel, hcard]

end Reindex

/-! ## The rewired displacement lemma -/

section Rewire

variable {Γ : Type} [Group Γ] {E : Type u} [Group E]

/-- The natural coordinate dimension of a stage. -/
def natDim (B : OpAlmostRepresentation E) (n : ℕ) : ℕ := Fintype.card (B.model n)

theorem natDim_pos (B : OpAlmostRepresentation E) (n : ℕ) : 0 < natDim B n :=
  B.modelNonempty n

/-- The chosen coordinate bijection at each stage. -/
noncomputable def natEquiv (B : OpAlmostRepresentation E) (n : ℕ) :
    B.model n ≃ Fin (natDim B n) :=
  Fintype.equivFin (B.model n)

/-- The almost representation read in the natural coordinates
`M_{d n}(ℂ)` that `manuscriptKazhdanTransport` is stated over. -/
noncomputable def natRep (B : OpAlmostRepresentation E) (n : ℕ) (g : E) :
    Matrix.unitaryGroup (naturalFiniteModel (natDim B n)) ℂ :=
  unitaryReindexEquiv (natEquiv B n) (B.map n g)

@[simp] theorem natRep_coe (B : OpAlmostRepresentation E) (n : ℕ) (g : E) :
    ((natRep B n g : Matrix.unitaryGroup (naturalFiniteModel (natDim B n)) ℂ) :
        Matrix (naturalFiniteModel (natDim B n))
          (naturalFiniteModel (natDim B n)) ℂ)
      = matrixReindexStarAlgEquiv (natEquiv B n)
          (B.map n g : Matrix (B.model n) (B.model n) ℂ) := rfl

theorem natRep_asymptoticallyMultiplicative (B : OpAlmostRepresentation E)
    (g h : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N,
      ‖(natRep B n (g * h) : Matrix (naturalFiniteModel (natDim B n))
            (naturalFiniteModel (natDim B n)) ℂ) -
        (natRep B n g : Matrix (naturalFiniteModel (natDim B n))
            (naturalFiniteModel (natDim B n)) ℂ) * natRep B n h‖ ≤ ε := by
  obtain ⟨N, hN⟩ := B.asymptoticallyMultiplicative g h ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have hrw : (natRep B n (g * h) : Matrix (naturalFiniteModel (natDim B n))
          (naturalFiniteModel (natDim B n)) ℂ) -
        (natRep B n g : Matrix (naturalFiniteModel (natDim B n))
          (naturalFiniteModel (natDim B n)) ℂ) * natRep B n h
      = matrixReindexStarAlgEquiv (natEquiv B n)
          ((B.map n (g * h) : Matrix (B.model n) (B.model n) ℂ) -
            (B.map n g : Matrix (B.model n) (B.model n) ℂ) * B.map n h) := by
    simp only [natRep_coe, map_sub, map_mul]
  rw [hrw, norm_matrixReindexStarAlgEquiv]
  exact hN n hn

theorem natRep_norm_le_one (B : OpAlmostRepresentation E) (n : ℕ) (g : E) :
    ‖(natRep B n g : Matrix (naturalFiniteModel (natDim B n))
        (naturalFiniteModel (natDim B n)) ℂ)‖ ≤ 1 :=
  norm_le_one_of_mem_unitary (natRep B n g).2

/-- The transport's hypothesis `_hx`, in natural coordinates, at the root
element `x_n = V_c`. -/
theorem natRep_centralRoot_hsCommutator (B : OpAlmostRepresentation E)
    (C : KazhdanCompressionCore Γ E) (γ : Γ) :
    KazhdanAsymptoticCommutant.NaturalHSCommutatorVanishing (natDim B) (natRep B)
      (fun n ↦ (natRep B n C.c : Matrix (naturalFiniteModel (natDim B n))
        (naturalFiniteModel (natDim B n)) ℂ)) (C.iota γ) := by
  intro ε hε
  obtain ⟨N, hN⟩ := centralRoot_commutator_hsNormSq_vanishing B C γ ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have hrw : (natRep B n C.c : Matrix (naturalFiniteModel (natDim B n))
          (naturalFiniteModel (natDim B n)) ℂ) * natRep B n (C.iota γ)
        - (natRep B n (C.iota γ) : Matrix (naturalFiniteModel (natDim B n))
          (naturalFiniteModel (natDim B n)) ℂ) * natRep B n C.c
      = matrixReindexStarAlgEquiv (natEquiv B n)
          ((B.map n C.c : Matrix (B.model n) (B.model n) ℂ) * B.map n (C.iota γ)
            - (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
              * B.map n C.c) := by
    simp only [natRep_coe, map_sub, map_mul]
  rw [hrw, hsNormSq_matrixReindex]
  exact hN n hn

/-- **INT.03 and INT.04, the rewired step.**  The Appendix-B displacement lemma
`KazhdanCompressorCorner.transportedRoot_displacement_hsDistSq_vanishing`,
re-proved through the printed §3 ultraproduct route.

The proof is one application of
`KazhdanAsymptoticCommutant.manuscriptKazhdanTransport` -- which is itself
derived by `ultraproductKazhdanTransport`, the printed proof -- at `s = t` and
`x_n = V_c`, followed by unitary invariance.  No spectral corner, no reversal
estimate and no explicit constant appears.

The statement is character-for-character the Appendix-B lemma's, so replacing
that lemma by this one inside
`KazhdanCompressorCorner.compressionDefect_hsDistSq_vanishing` exchanges the
route of `LiteralNonMFEndpoint.kazhdanPinning` without touching any endpoint. -/
theorem transportedRoot_displacement_ultraproduct
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E) (γ : Γ) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      hsDistSq (B.model n)
        ((B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) *
          lampMatrix B C n *
          (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ)
        (lampMatrix B C n) ≤ ε := by
  refine transportedRoot_displacement_of_hsCommutator B C γ ?_
  -- The representation universe of property `(T)` is pinned explicitly: it
  -- occurs only in this hypothesis, so leaving it to unification would leave a
  -- universe metavariable in the proof term.  `manuscriptKazhdanTransport` is
  -- polymorphic in it, so any instantiation is available.
  have hT : HasKazhdanPropertyTComplex.{0, 0} Γ :=
    hasKazhdanPropertyT_iff_textbook.mp C.kazhdan
  have hconc := KazhdanAsymptoticCommutant.manuscriptKazhdanTransport
    hT C.iota C.t C.compresses (natDim B) (natDim_pos B) (natRep B)
    (natRep_asymptoticallyMultiplicative B)
    (fun n ↦ (natRep B n C.c : Matrix (naturalFiniteModel (natDim B n))
      (naturalFiniteModel (natDim B n)) ℂ))
    ⟨1, zero_le_one, fun n ↦ natRep_norm_le_one B n C.c⟩
    (natRep_centralRoot_hsCommutator B C) γ
  intro ε hε
  obtain ⟨N, hN⟩ := hconc ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have key : hsNormSq (B.model n)
        (lampMatrix B C n *
            (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
          - (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) *
            lampMatrix B C n)
      = hsNormSq (naturalFiniteModel (natDim B n))
          ((natRep B n C.t : Matrix (naturalFiniteModel (natDim B n))
                (naturalFiniteModel (natDim B n)) ℂ) *
              (natRep B n C.c : Matrix (naturalFiniteModel (natDim B n))
                (naturalFiniteModel (natDim B n)) ℂ) *
              (natRep B n C.t : Matrix (naturalFiniteModel (natDim B n))
                (naturalFiniteModel (natDim B n)) ℂ)ᴴ *
              (natRep B n (C.iota γ) : Matrix (naturalFiniteModel (natDim B n))
                (naturalFiniteModel (natDim B n)) ℂ)
            - (natRep B n (C.iota γ) : Matrix (naturalFiniteModel (natDim B n))
                (naturalFiniteModel (natDim B n)) ℂ) *
              ((natRep B n C.t : Matrix (naturalFiniteModel (natDim B n))
                  (naturalFiniteModel (natDim B n)) ℂ) *
                (natRep B n C.c : Matrix (naturalFiniteModel (natDim B n))
                  (naturalFiniteModel (natDim B n)) ℂ) *
                (natRep B n C.t : Matrix (naturalFiniteModel (natDim B n))
                  (naturalFiniteModel (natDim B n)) ℂ)ᴴ)) := by
    rw [← hsNormSq_matrixReindex (natEquiv B n)]
    congr 1
    simp only [lampMatrix, map_sub, map_mul, matrixReindex_conjTranspose,
      natRep_coe]
  rw [key]
  exact hN n hn

end Rewire

end

end UltraproductRigidityRoute
end GroupApproximation
