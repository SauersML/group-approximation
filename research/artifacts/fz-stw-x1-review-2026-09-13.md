# STW Problem X(1): fidelity review of `not_problemX1Statement` (2026-09-13)

Lane `x1-fidelity`, fz wave 2. **Verdict: PASS.** The Lean endpoint answers the printed question
in the negative, and its trace definitions match Brown's. There are three presentation caveats
(universe, one docstring citation, priority wording). None of them changes the verdict.

Base: main `ac4ce20dd` (tip at review time). The content of `ProblemX.lean`, `ProblemXWitness.lean`,
`ProblemXGroups.lean`, `TikuisisWhiteWinterCore.lean` and `QuasidiagonalTrace*.lean` is unchanged since
`390ffa310` (2026-09-05); the `becc912bd`/`3f71a3a50` delete-and-restore of 09-12 round-trips them.

## Sources read

- C. Schafhauser, A. Tikuisis, S. White, *Nuclear C\*-algebras: 99 problems*, arXiv:2506.10902v2.
  I read Problem X and the paragraphs around it (pp. 14–15) from `pdftotext` output.
- N. P. Brown, *Invariant means and finite representation theory of C\*-algebras*, Mem. AMS 184
  (2006), arXiv:math/0304009v2. I read the standing assumptions, Definition 3.1.1, Theorem 3.1.6,
  Definition 3.3.1 and Theorem 4.1.9.
- N. Ozawa, *The hyperfinite II1 factor is not quasidiagonal*, arXiv:2609.08892v1 (8 Sep 2026).
- Eckhardt, arXiv:2608.28772v1 (28 Aug 2026).

## 1. Printed text and standing assumptions

STW v2, p. 15:

> Problem X. (1) Are amenable traces on C∗-algebras necessarily quasidiagonal?

The problem has no hypotheses. The next paragraph says X(1) "easily reduces to the case of
separable C∗-algebras". STW credit quasidiagonal traces to Brown's memoir (their [52]). For X(1)
they cite [52, Discussion before Proposition 3.5.1] and note that a positive answer would imply a
positive answer to IX(1). A trace here is a tracial state, as in Brown's T(A).

Brown's memoir assumes that all C\*-algebras are unital and separable, unless stated otherwise.
The repository's witness is unital and separable, so it lies inside Brown's standing assumptions
and answers the unrestricted printed question.

## 2. Brown's definitions

Let A be unital and separable, and let T(A) be its tracial states. tr_k is the normalized trace on
M_k(ℂ), and ‖x‖₂ = tr_k(x\*x)^{1/2}.

- **Amenable trace (Definition 3.1.1).** Represent A concretely in B(H). A state τ on A is an
  amenable trace if some state φ on B(H) extends τ and satisfies φ(uTu\*) = φ(T) for every
  unitary u ∈ A and every T ∈ B(H). By Proposition 3.1.2 this does not depend on the
  representation.
- **Sequence form (Theorem 3.1.6, (1)⇔(2)).** For τ ∈ T(A), τ is amenable if and only if there are
  u.c.p. maps φn : A → M_{k(n)}(ℂ) with ‖φn(ab) − φn(a)φn(b)‖₂ → 0 and tr_{k(n)}(φn(a)) → τ(a)
  for all a, b.
- **Quasidiagonal trace (Definition 3.3.1).** τ ∈ T(A) is quasidiagonal if there are u.c.p. maps
  φn : A → M_{k(n)}(ℂ) with tr_{k(n)} ∘ φn → τ weak-\* and ‖φn(ab) − φn(a)φn(b)‖ → 0 for all a, b.
- **Kirchberg (Theorem 4.1.9).** A discrete group Γ has the factorization property if and only if
  the canonical trace on C\*(Γ) is amenable.

Right after Definition 3.3.1, Brown writes that he does not know whether every amenable trace is
quasidiagonal. That is STW X(1).

## 3. Repository definitions (main `35c746f8e`)

```lean
def ProblemX1Statement : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] (τ : TracialState A),
    Quasidiagonal.IsAmenableTrace (fun a : A ↦ τ a) →
      Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a)
theorem not_problemX1Statement : ¬ ProblemX1Statement.{1}
```

`IsAmenableTrace τ` is `Nonempty (AmenableTraceModel τ)`, and `IsQuasidiagonalTrace τ` is
`Nonempty (QuasidiagonalTraceModel τ)`. The two structures differ only in the multiplicativity
clause.

| Clause | Lean field | Brown |
| --- | --- | --- |
| sizes | `space : ℕ → FiniteModel` | k(n) |
| maps | `map n : A →ₗ[ℂ] Matrix (space n) (space n) ℂ` | φn |
| unital | `map_one` | u.c.p. |
| positivity | `completelyPositive`, i.e. `IsCompletelyPositiveOnMatrices` (form sense) | c.p. |
| amenable defect | `tendsto_mul_hs`: `hsNorm (…) → 0` | ‖·‖₂ → 0 |
| QD defect | `tendsto_mul`: `‖…‖ → 0` under `Matrix.Norms.L2Operator` | operator norm → 0 |
| trace | `tendsto_trace`: `‖τ a − normTrace (space n) (map n a)‖ → 0` | tr_{k(n)} ∘ φn → τ |

`TracialState A` (Analysis/ShulmanTraceClasses.lean) is a ℂ-linear map with τ(1) = 1,
τ(x\*x) ≥ 0 and τ(xy) = τ(yx). Mathlib's `CStarAlgebra` is unital.

## 4. Clause-by-clause comparison

For unital separable A and τ ∈ T(A), the Lean predicates are equivalent to Brown's:
repo-amenable ⇔ Brown-amenable and repo-QD ⇔ Brown-QD. The refutation needs only
repo-amenable ⇒ Brown-amenable and Brown-QD ⇒ repo-QD.

1. **Complete positivity.**
   - The Lean condition says Σ_{i,j,x,y} conj(w_{ix}) φ(a_i\* a_j)_{xy} w_{jy} is real and ≥ 0 for
     every tuple a : Fin m → A and every w : Fin m → Y → ℂ.
   - That makes [φ(a_i\* a_j)] positive in M_m(M_k) for every tuple.
   - The positive elements of M_m(A) are finite sums of matrices [a_i\* a_j]. So this is complete
     positivity.
   - C.p. maps are bounded, so omitting a continuity clause loses nothing.
2. **Hilbert–Schmidt norm.**
   - `hsNorm Y x = √((Σ_{i,j} |x_ij|²) / card Y)` (Sofic/LeavittTraceFloor.lean and
     Sofic/HyperlinearScalar.lean). This is tr_k(x\*x)^{1/2} for the normalized trace, i.e.
     Brown's ‖·‖₂.
   - The driver checks this formula against the field.
3. **Operator norm.**
   - `QuasidiagonalTrace.lean` opens `Matrix.Norms.L2Operator` before the structure. On
     `Matrix Y Y ℂ` that norm is the C\*-norm of M_k.
   - The driver re-elaborates the field under the same scope.
4. **Trace convergence.** Weak-\* convergence of tr ∘ φn to τ is pointwise convergence on A, which
   is `tendsto_trace`. `normTrace Y x = trace x / card Y` is tr_k.
5. **Empty models.**
   - Lean models may have `card (space n) = 0`; Brown's may not.
   - For a tracial state, `tendsto_trace` at a = 1 gives normTrace(φn(1)) → 1. An empty model has
     normTrace 0, so only finitely many models are empty. Dropping them gives Brown's sequence.
   - Brown's models are Lean models as they stand.
   - Without the state bundle the predicates would be vacuous: `isQuasidiagonalTrace_zero` makes the
     zero functional quasidiagonal, and hence amenable, through empty models. `ProblemX1Statement`
     bundles `τ : TracialState A`, which rules this out.
6. **Trace class.** `TracialState` is Brown's T(A): linear, unital, positive on x\*x (hence positive
   and bounded on a C\*-algebra) and tracial.
7. **Sequences versus nets.**
   - Brown's sequence form is stated for separable A. `ProblemX1Statement` quantifies over all A.
   - A refutation needs only one witness, and
     `literalCanonicalTrace_separable_amenable_not_quasidiagonal` provides a separable one.

So `¬ ProblemX1Statement.{1}` says that some unital C\*-algebra `A : Type 1` has a tracial state
that is amenable but not quasidiagonal in Brown's sense. That is a negative answer to printed X(1).

## 5. Proof chain

`not_problemX1Statement` (ProblemX.lean) is
`not_problemX1Statement_of_literalFactorizationProperty literalFactorizationProperty`. The bridge
applies the assumed X(1) to `canonicalMaximalTracialState MarkedGroup` on
`MaximalGroupCStar MarkedGroup`, where `MarkedGroup` is the literal finitely presented group E.

- **Amenable.** `literalFactorizationProperty` is
  `LocallyRFByIntFactorization.canonicalMaximalTrace_isAmenableTrace_of_locallyRFByInt`, applied to
  the stable-letter decomposition of E (`StableLetterLEFRoute.shiftAction`,
  `markedGroupEquivKernelByInt` and `telescopeKernel_locallyResiduallyFinite`). The models with small
  HS defect are built directly; this is the direction of Brown's Theorem 4.1.9 that the proof uses.
- **Not quasidiagonal.** `literalCanonicalTrace_not_isQuasidiagonalTrace` combines
  `Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace` (with `ucpContractive`), which says a QD trace
  is an MF trace, with `LiteralTraceConsequence.markedGroup_canonicalMaximalTrace_not_isMFTrace`.
- **Existential form.** `amenableNonQuasidiagonalTrace : AmenableNonQuasidiagonalTrace.{1}`
  (ProblemXWitness.lean) adds `SeparableSpace` to the witness.
  `not_problemX1Statement_of_amenableNonQuasidiagonalTrace` derives the negation from it without
  excluded middle.
- **Gates.** ProblemX.lean has `#audit_closed_axioms` on `not_problemX1Statement`,
  `literalFactorizationProperty` and `literalCanonicalTrace_not_isQuasidiagonalTrace`.
  ProblemXWitness.lean has one on `amenableNonQuasidiagonalTrace`. The driver re-prints both
  endpoint closures (Section 7).

## 6. Universe

`MaximalGroupCStar G : Type (u+1)`, because it is a closure inside `MaximalGroupCStarAmbient G`.
So the endpoint is `¬ ProblemX1Statement.{1}`.

This is harmless mathematically: the printed question has no universe, and a counterexample in
`Type 1` is a counterexample. Formally, though, `¬ ProblemX1Statement.{1}` and
`¬ ProblemX1Statement.{0}` are different propositions, and at the Mathlib pin there is no `ULift`
C\*-algebra instance to pass between them.

The witness can be moved to `Type 0`:

1. **`Small.{0}`.** The witness is separable. Take a dense sequence d; then a ↦ (n ↦ dist a (d n))
   is injective into ℕ → ℝ, and `small_of_injective` applies (Mathlib/Logic/Small/Basic.lean).
2. **`CStarAlgebra (Shrink A)`.**
   - Ring and algebra structure: Mathlib/Algebra/Algebra/Shrink.lean.
   - Norm: `NormedRing.induced` and `NormedAlgebra.induced`.
   - `CStarRing`, `CompleteSpace` and `StarModule` need short transport proofs.
3. **Transport along `Shrink A ≃⋆ₐ[ℂ] A`.**
   - `IsQuasidiagonalTrace.comp` and `QuasidiagonalTraceModel.compStarAlgHom`
     (QuasidiagonalTraceProperties.lean) pull quasidiagonality back along a unital
     ⋆-homomorphism. Applied to the inverse, they carry non-quasidiagonality across.
   - The amenable clause needs the same pullback for `AmenableTraceModel`, by the same proof.
     `git grep` at the tip finds no `IsAmenableTrace.comp` or `AmenableTraceModel.comp*`.

**Recommendation.** State the Palomar answer at `Type`: either `¬ ProblemX1Statement.{0}`, or an
existential over `A : Type` with `SeparableSpace A`, a bundled `TracialState`, amenable and not
quasidiagonal. If the transport is not built, keep `.{1}` and explain it in the docstring.

## 7. Model tests

The driver is `GroupApproximation/Manuscript/NinetyNineProblems/X1FidelityDriver.lean` (md5
`6043a58bd08718cbfd3fc749db6199d3`). It is probe-only and not landed. Probe `x1-fidelity`: tag
`0913-031038-29406`, base `8389a0e6c`, PROBE GREEN, 8 of 8 closures printed.

| Kind | Declaration | Content | Result |
| --- | --- | --- | --- |
| positive | `matricial_trace_isQuasidiagonal` | normTrace on M_Y(ℂ) is QD | GREEN |
| positive | `matricial_tracialState_amenable_and_quasidiagonal` | some `TracialState` on M_Y(ℂ) is amenable and QD | GREEN |
| negative | `shifted_functional_not_amenable` | z ↦ z + 1 on ℂ is not amenable | GREEN |
| negative | `corner_functional_not_quasidiagonal` | a ↦ a₀₀ on M₂(ℂ) is not QD (not tracial) | GREEN |
| vacuity | `zero_functional_passes_both_clauses` | 0 passes both clauses via empty models | GREEN |
| bundle | `zero_functional_not_tracialState` | 0 is not a tracial state | GREEN |
| pins | four `example`s | op-norm clause, HS formula, `.{1}` endpoint, `.{1}` separable witness | GREEN |

Axiom closures: all eight declarations print `[propext, Classical.choice, Quot.sound]`. That is
the two endpoints and the six driver theorems. The first probe was red only on
`corner_functional_not_quasidiagonal`, where a `!![…]` argument had no type ascription. The fixed
file is the one recorded GREEN.

## 8. The two audit artifacts

**`stw10-x1-refutation-hostile-audit-2026-08-30.md`**
- It checks three dangers in the factorization-property chain and finds each closed:
  - finitely many trace conditions per stage;
  - local residual finiteness rather than LEF;
  - transport of relative property (T).
- It records that the refutation leaves IX(1), VII and X(2) untouched, because C\*(E) is not
  nuclear.
- I found nothing in it that conflicts with the Lean chain.
- Its remark that X(2) is open is now out of date (Section 9).

**`stw10-x1-exact-residual-2026-09-05.md`**
- It transcribes Problem X with STW's surrounding remarks. The transcription matches the v2 text
  extracted here.
- It argues that the group-algebra mechanism cannot reach exact algebras: for exact A, amenability
  of τ is injectivity of π_τ(A)'', and L(E) is not injective.
- It leaves the exact case of X(1) open. This review does not change that.

## 9. Priority (search refreshed to 2026-09-13)

This was a bounded web and arXiv search: amenable traces, quasidiagonal traces, Brown's question,
and citations of STW Problem X.

| Date | Item | Relation to X(1) |
| --- | --- | --- |
| 2026-08-27 | repo commit `2dbea8f73` | states X(1) against the literal group |
| 2026-08-28 | Eckhardt, arXiv:2608.28772v1 | W = (⊕_{G/Γ} ℤ/2) ⋊ G is not MF and C\*(G) is not finite; no claim about the factorization property, amenable traces or X(1) |
| 2026-08-30 | hostile audit artifact | audits the chain |
| 2026-08-31 | repo commit `4830b808c` | proves the X(1) counterexample |
| 2026-09-08 | Ozawa, arXiv:2609.08892v1 | an MF algebra A with A ⊗ R infinite, so R is not quasidiagonal; answers the problem of Brown's Section 6.6, i.e. STW X(2) |

Ozawa cites Problem X of STW for the problem he answers, but he states no result on X(1). His
theorem does imply a negative answer to X(1) through STW's remark: τ_R is amenable and, by his
result, not quasidiagonal. The repository commits come 12 and 8 days before his preprint.

Other hits screened, none of which answers X(1): Neagu arXiv:2211.01666, Moradi–Amini
arXiv:2606.13924, Paulsen–Rahaman–Samei arXiv:2606.18369, and arXiv:1904.13133.

## 10. Corrections and follow-ups

1. **Docstring citation.**
   - The `AmenableTraceModel` docstring (TikuisisWhiteWinterCore.lean) cites Brown–Ozawa, Chapter 6.
   - The structure actually transcribes Brown's Theorem 3.1.6(2), which the docstring of
     `ProblemX1Statement` cites correctly.
   - Add Theorem 3.1.6(2) to the Core docstring. The `QuasidiagonalTraceModel` docstring cites only
     Tikuisis–White–Winter; add Brown's Definition 3.3.1 there.
   - This is a citation fix, not a mathematical error.
2. **Universe.** State the Palomar answer at `Type` via the transport in Section 6, or document
   `.{1}`.
3. **Priority wording.**
   - Credit Ozawa with X(2). Describe his consequence for X(1) as a corollary through STW's remark.
   - The hostile audit's statement that X(2) is open is superseded. That goes to team-lead; the
     artifact is not edited.
