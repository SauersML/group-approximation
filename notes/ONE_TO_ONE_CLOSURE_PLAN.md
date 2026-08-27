# Closing the 1:1 gap: what the ledger's non-`EXACT` rows actually are

Date: 2026-08-16.  Companion to `notes/NON_MF_PROOF_LEDGER.md`, which records the
audit; this document reads the audit's output as a work list and says, for every
non-`EXACT` row, what would close it and how large that is.

The ledger says the project is 1:1 only when every row is `EXACT` in both
columns, and that this is not the present state.  It does not say how far from
it we are, or whether the distance is one project or a hundred.  It is four
projects and a short list, and two of the four cover 56 of the 132 non-`EXACT`
statement rows.

## The census

506 step rows.  Statement column: 374 `EXACT`, 69 `MISMATCH`, 63 `MISSING`.

| Class | Rows | Anchors | What closes it |
|---|---|---|---|
| **A. Prose context** | 34 `MISSING` | 25 `p:` anchors | Nothing. Correct as recorded |
| **B. `univ0`** | 31 `MISMATCH` | 27 | One transfer lemma |
| **C. Ultraproduct scaffolding** | 16 `MISSING` + 9 `MISMATCH` | `thm:kazhdan-transport` | Operator-algebra ultraproducts in Mathlib |
| **D. Named per-item gaps** | 13 `MISSING` | 8 | A bounded lemma each |
| **E. Decomposition mismatches** | 29 `MISMATCH` | ~20 | Re-decompose the Lean proof, or the printed one |

Classes A and E are not defects.  A is literature and history: sentences like
`p:intro-history`, `p:intro-cde`, `p:undec-adianrabin` have no formal content to
bind, and marking them `MISSING` is the ledger being honest, not the project
being incomplete.  E is the ledger's own rule 2 — a printed step is `MISMATCH`
when Lean proves the enclosing theorem by a different decomposition, even where
the enclosing conclusion is `EXACT`.  Closing E means making two proofs
step-for-step congruent, which buys audit tidiness and no mathematics.

The work is B, C and D.

## B. `univ0` — 31 rows, one lemma

The ledger's rule 1: where the manuscript says "let `H` be a countable group"
and the Lean reads `{H : Type}`, the formal assertion is strictly narrower, so
the row is `MISMATCH`.  The transfer is true and routine and deliberately not
assumed.

It spans 27 anchors, including `thm:kazhdan-transport`, `thm:sign-criterion`,
`thm:criterion`, `thm:collapse`, `thm:normal-kazhdan`, `thm:saturation`,
`thm:compression-radical`, `thm:projection-collapse`, `thm:torsion-collapse`,
`thm:B` and `cor:generaltransport` — that is, most of the mechanism.  One lemma
in the development turns all 31 into `EXACT`:

```
theorem exists_type0_model (G : Type u) [Group G] [Countable G] :
    ∃ (G₀ : Type) (_ : Group G₀), Nonempty (G ≃* G₀)
```

`Countable G` gives `Small.{0} G`, `Shrink.{0} G` is the carrier, and
`Equiv.mulEquiv` transports the group structure along `equivShrink`.  Each
`Type 0` theorem then yields its universe-polymorphic form by composing with the
isomorphism-invariance the development already has: `isOperatorMF_of_mulEquiv`,
`isResiduallyFinite_of_mulEquiv`, `HasKazhdanPropertyT.of_mulEquiv`,
`Group.IsFinitelyPresented.equiv`, and `mem_fdUnitaryResidual_mulEquiv`.  What
is missing is the transfer itself and, for each property that lacks one, the
invariance lemma.

Size: one small module plus a corollary per headline theorem.  No new
mathematics.  This is the single highest-leverage item in the project.

## C. The ultraproduct scaffolding — 25 rows, one Mathlib-scale project

`thm:kazhdan-transport` carries 30 ledger rows, and only 4 are `EXACT`.  The
sixteen `MISSING` ones are the printed proof's apparatus and nothing else:

* form the Hilbert-space ultraproduct `K_ω` of the `K_n` along `ω` (KT.05);
* form the norm ultraproduct `B_ω = ∏_ω B(K_n)` acting on it (KT.06);
* that action is faithful (KT.07);
* `ran P ⊆ ran Q` gives `QP = P` for projections of `B_ω` (KT.08);
* `π(g) = [Ad U_n(g)]_ω` is a homomorphism into `U(B_ω)` (KT.09);
* **`B_ω` is finite** — the step the whole theorem turns on (KT.10);
* the isometry `σ = r + (1 − Q)` and its unitarity (KT.21, KT.22);
* the subsequence-to-full-sequence closing argument (KT.28).

None of this exists in Lean, here or in Mathlib.  The development instead proves
the theorem through the corner machinery (`KazhdanCompressorCorner`,
`KazhdanCornerMatrices`, `WeakMFVectorGNS`), which is why the same anchor also
carries 9 `MISMATCH` rows: the Lean route is real but is not the printed route.

Two honest options, and they are not equivalent.

**C1. Formalize the apparatus.**  Hilbert-space ultraproducts, the norm
ultraproduct of a bounded family of `B(H_n)`, faithfulness, and finiteness.
Mathlib has `Filter.Germ` and ultrafilter limits but no operator-algebra
ultraproduct.  This is the multi-month item.  It would close 16 rows here and
would be reusable well beyond this paper.

**C2. Promote the finite-stage proof to primary.**  `app:finite-stage` already
prints a quantitative proof at each coordinate, and the corner machinery that
implements it is formalized.  Tempting, and *not* a clean substitution: that
appendix states its own caveat — property (T) constrains exact unitary
representations, while at a finite stage the matrix models only generate a
representation of the free group on `S`, so the spectral-gap input is granted
per stage rather than proved there.  Promoting the finite-stage proof would move
the limit out of the printed argument and into an admitted hypothesis, which is
a worse trust surface, not a better one.  The collapse theorem could take this
route (and now does, in its Step 6) precisely because its gap input arrives from
the ambient Kazhdan pair rather than from the stage.

Recommendation: C1, and until it lands, the manuscript should say in one
sentence that the printed proof of Theorem 3.1 is not the formalized route and
that the formalized route is the corner argument of `app:finite-stage`.  That
sentence does not exist today, and its absence is the largest single overstatement
of formal coverage in the paper.

## D. The named per-item gaps — 13 rows, eight bounded lemmas

| Anchor | Rows | Obligation |
|---|---|---|
| `prop:literal-base-T` | 2 + 5 | the gap places `sp(Δ)` in `{0} ∪ [1/500, ∞)` — the rational certificate's spectral step |
| `rem:ff-realization` | 3 | Fournier-Facio's f.p. torsion-free (T) group contains every f.p. torsion-free group; literature interface |
| `lem:lift` | 2 | polar correction: `‖x*x − 1‖ ≤ 1/2` gives a unitary `u = x(x*x)^{-1/2}` at controlled distance |
| `rem:invariantsize` | 2 | cardinality on subgroups of a finite group is a conjugation-invariant size |
| `cor:uniform` | 1 | an effective modulus for the compactness argument — recorded as open, and genuinely open |
| `thm:transport-variants` | 1 | "the ultraproduct proof applies verbatim" — inherits C |
| `rem:chaincondition` | 1 | Zariski-closed subgroups of `GL(V)` satisfy the descending chain condition |
| `rem:classical-base` | 1 | CRW/CLV attribution; literature, not an obligation |

Of these, `lem:lift`, `rem:invariantsize` and `rem:chaincondition` are ordinary
lemmas that could be written this week.  `prop:literal-base-T` is the interesting
one: the certificate is printed and checked numerically, and formalizing the
spectral step is the difference between an audited certificate and a quoted one.
`cor:uniform` and `rem:ff-realization` should stay `MISSING`; they are honest.

## What "ideal" means, stated as a target

1. Class B closed — the development quantifies over the same groups the paper does.
2. Class C either closed (C1) or declared in print, in one sentence, at the theorem.
3. Class D closed except `cor:uniform` and the two literature interfaces.
4. Class E left alone unless a decomposition happens to be rewritten anyway.
5. Class A left alone permanently.

That is 44 rows of real work plus one Mathlib-scale project, against 374 rows
already `EXACT`.  The paper's mathematics is not in question in any of it: no row
in the census says a printed step is *wrong*.  Every one says a printed step is
either unformalized, formalized differently, or formalized more narrowly.
