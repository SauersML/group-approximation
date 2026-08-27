# External audit of the hyperlinear/sofic program, and two exact atlas results

Date: 2026-08-16.  Working notes, not canonical.

Source: an external full-corpus audit of a snapshot archive
(`group-approximation-main (7).zip`, SHA-256
`16e568da66f6e8c951d401187d758dacdf7883762f5cd2d97ca0eaef5384bea3`),
re-checked against live `main` at `dd28ae61` before landing here.  Two of the
audit's findings are new mathematics and became graph nodes
(`atlas-stabilizer-slice-stationary`, `atlas-stabilizer-commutant-no-go`,
plus the elementary `atlas-defect-gap-limit`); the rest is verification, and
two of its status findings were **already stale** by the time it was written.

---

## (a) Bottom line, unchanged

Pestov Question 3.4 is **open** as of 2026-08-16.  Neither answer is in hand:
no hyperlinear nonsofic group, and no proof that hyperlinearity implies
soficity.  The graph's `q3-4-resolved` goal and both answer claims
(`hyperlinear-nonsofic-group`, `hyperlinear-implies-sofic`) are correctly
marked open, and the external literature agrees — the OpenAI chapter's own
sentence, verbatim in both released versions, is that Theorem 1.1 "does not
determine whether `L_(F₂)(1,2)^×` is hyperlinear."

What changed since 2026-08-01 is only the *nonsofic* side: nonsofic groups now
exist unconditionally (Kun–Thom wreaths, the Leavitt unit group,
Fournier-Facio's torsion-free examples).  Soficity implies hyperlinearity;
the converse is the question, and no nonsoficity result touches it.  Recorded
already on `hyperlinear-nonsofic-group`; nothing to revise there.

## (b) Snapshot-vs-live corrections (both in the repo's favour)

1. **The Steinberg presentation gap is closed.**  The archive still shows the
   rank-five spare-index/completeness hole ("Lemma X") as the frontier.  It
   was closed later the same day by a joint induction, with the missing
   additive involutivity relations repaired:
   `atlas-steinberg-spare-index-independence` is ESTABLISHED and
   `atlas-steinberg-rank-five-translation` delivers `T_St` explicitly.  Do not
   re-attack it.

2. **The last Lean `sorry` is gone.**  The audit reports exactly one literal
   `sorry` in `GroupApproximation/` — `isNormApproximable_of_isMFRegularCharacter`
   in `Sofic/MFTraceRecognition.lean`.  That was true of the snapshot; commit
   `1da7fd1f` ("Close the MF-trace recognition sorry", 2026-08-16) discharged
   it.  A `grep -r sorry --include=*.lean` over live `main` returns **zero**
   hits, repo-wide.  Either way the audit's own reading was right: that
   theorem is MF trace recognition and is not a step of Q3.4.

Counts in the snapshot, for the record: 1,108 Markdown files, 986 Lean files.
Live `main` is at 1,131 Markdown and 1,045 Lean.

**Relator arithmetic, reconciled.**  The audit quotes 4,648 and 72; both are
right and they count different things.  `|T_St| = 4,648` = 4,612 Steinberg
product relators + 24 involutivity relators + 12 reverse-dictionary relators.
The probe JSON carries 4,636 (all but the reverse-dictionary twelve), of which
exactly **72** escape `ker(P̄ ↠ A₈ × A₈)` and are the active set at the tensor
flip — the set identified in `atlas-true-criterion-baseline`.

## (c) The criterion, and why there are no magic multiplicities

With `P̄ = A₈ * A₈` the two-chart atlas source and `λ` the 20,160-dimensional
regular representation of `A₈`, define for `U ∈ U(20160k)` the exact
free-product representation

```
π_U(h) = λ(h) ⊗ I_k            (h ∈ K₁)
π_U(h) = U (λ(h) ⊗ I_k) U*     (h ∈ K₂)
```

and

```
d_k = min_{U ∈ U(20160k)}  max_{s ∈ T_St}  ‖π_U(s) − I‖₂ .
```

The repository's criterion (`atlas-steinberg-rank-five-translation` on top of
`atlas-relator-central-sufficiency`) then reads

```
Q hyperlinear   ⟺   leavitt-steinberg-hs-unstable   ⟺   inf_k d_k = 0 .
```

Two elementary facts about `d_k` were not previously recorded and are now
`atlas-defect-gap-limit`:

- **`d_k > 0` for every fixed `k`.**  `U(20160k)` is compact and the objective
  continuous, so the min is attained; at a zero of it every relator holds
  exactly, so `π_U` is a genuine `20160k`-dimensional unitary representation
  of `E = P̄/⟨⟨T_St⟩⟩ ≅ St₅(L)`, nontrivial because chart 1 is `λ ⊗ I_k`.
  Minimal almost periodicity of `E` forbids that.

- **Direct-sum subadditivity, hence a limit.**  Given `U ∈ U(20160k)` and
  `V ∈ U(20160ℓ)`, the direct sum is (after the basis permutation identifying
  `(λ ⊗ I_k) ⊕ (λ ⊗ I_ℓ)` with `λ ⊗ I_{k+ℓ}`, which conjugates both charts
  alike) a competitor at multiplicity `k + ℓ` with

  ```
  ‖π_{U⊕V}(s) − I‖₂² = ( k‖π_U(s) − I‖₂² + ℓ‖π_V(s) − I‖₂² ) / (k + ℓ) ,
  ```

  so `(k+ℓ) d_{k+ℓ}² ≤ k d_k² + ℓ d_ℓ²`.  Thus `k ↦ k d_k²` is subadditive and
  Fekete gives `lim_k d_k² = inf_k d_k²`.

The consequence is a search-design fact: there are **no isolated magic
multiplicities**.  A witness cannot hide at one exceptional `k`; the defect
either decays along all large multiplicities or is bounded below by a
dimension-free constant.  (Fekete gives the limit, not a rate, and says
nothing about which of the two holds.)

## (d) Result 1 — the Stage-1 `U(15)` slice is exactly first-order stationary

Setting.  Under `A₈ ≅ GL₄(𝔽₂)`, let `M < A₈` be the stabilizer of a nonzero
vector `e₀ ∈ 𝔽₂⁴`: `|M| = 1344`, index 15.  Decomposing `A₈` into the 15 right
cosets `M g_i` gives `ℓ²(A₈) ≅ ℓ²(M) ⊗ ℂ¹⁵` with `λ|_M ≅ λ_M ⊗ I₁₅`.  The
Stage-1 family of `atlas-true-criterion-baseline` §(d) is

```
U_t = D_t J ,     D_t = I_{ℓ²(M)} ⊗ e^{tK} ,     K* = −K  in  M₁₅(ℂ) ,
```

with `J` the tensor flip converting the second chart's left-regular copy into
the right-regular one, so that at `t = 0` a second-chart letter `b` acts as
`R_b`.

Differentiating.  `d/dt|₀ (D_t R_b D_t*) = [K, R_b]`.  For a relator `w`,
`f_w(t) = tr π_{U_t}(w)` differentiates to a sum over the second-chart
occurrences in `w`; cyclicity of the trace turns each occurrence into

```
Tr(K R_b Q P) − Tr(K Q P R_b) ,
```

with `P, Q` products of left/right regular permutations.  Since
`K = I_{ℓ²(M)} ⊗ k`, each such trace is an **exact integer pairing** of the
free `15 × 15` matrix `k` against a `15 × 15` transition-count matrix: the
whole derivative is computable in integer arithmetic, with no floating-point
question.

Result, over the 72 active relators of the snapshot family:

```
active relators                              72
second-chart derivative insertion sites    1,052
distinct transition-coefficient cases         40
relators with nonzero trace derivative         0
```

so `f_w'(0) = 0` for every tangent direction `K` and every active `w`, and
since `‖W − I‖₂² = 2 − 2 Re tr W` for unitary `W`, every active squared defect
is stationary at `J` too — relator by relator, not merely in the aggregate
loss.

This explains the MSI Stage-1 pilot (job 15868462: 60 Adam iterations moved
the total loss by `~1.1e-4`) **structurally**.  The pilot was not
under-optimized and its flatness was not optimizer noise; the gradient is
exactly zero there.  Reproduction script in the audit's own sandbox:
`atlas_stabilizer_stationarity_check.py` (not landed in this repo — the
statement below supersedes the need for it).

## (e) Result 2 — the whole stabilizer-commutant family is impossible, at every `k`

This is the substantive new theorem, and it subsumes §(d) as a search fence.

**Family.**  Fix `M` as above.  At multiplicity `k`, write
`H_k = ℓ²(A₈) ⊗ ℂ^k ≅ ℓ²(M) ⊗ ℂ^{15k}` and consider **any**

```
U = D J ,     D ∈ I_{ℓ²(M)} ⊗ U(15k) .
```

No monomiality, bounded complexity, proximity to `I`, or finite order is
assumed of `D`.  (The proof below uses only `[D, π₁(m)] = 1` for `m ∈ M`, so
it covers the strictly larger family `D ∈ π₁(M)′`, the full commutant of the
first chart's `M`-copy, of which `I_{ℓ²(M)} ⊗ U(15k)` is the corner Stage-1
actually searches.)

**Lemma (an exact cross-commutation is forced).**  `D` commutes with
`π₁(m) = λ(m) ⊗ I_k = λ_M(m) ⊗ I_{15k}` for every `m ∈ M`, hence with `D*`
likewise; and `J L_b J* = R_b` commutes with every left translation.  So for
all `m ∈ M`, `b ∈ A₈`,

```
[π₁(m), π₂(b)] = 1        exactly, throughout the family.        (*)
```

**The witness word.**  Take the first-chart transvection `p_{01} = I + E_{01}`,
which fixes `e₀` and so lies in `M`, and the second-chart transvection
`p_{10}`.  Put `c = [p₁_{01}, p²_{10}]`, of free-product length 4.  The
repository's exact binary-Leavitt normal-form evaluator returns 12 surviving
monomials and `leavitt_is_one = False`: **`c` maps to a nonidentity element of
`Q`**.  (Consistency check: `c` lies in `ker(P̄ ↠ A₈ × A₈)`, as it must — it
is a commutator of elements from different charts — so it is not a relator
and its nontriviality in `Q` is exactly the cartesian-escape phenomenon that
`atlas-kernel-window-length-nine` and `atlas-true-criterion-baseline` already
localize.)

**Theorem.**

```
inf_{k ≥ 1, D ∈ π₁(M)′}  max_{s ∈ T_St} ‖π_{DJ}(s) − I‖₂  >  0 .
```

*Proof.*  Suppose not: take `k_n` and `D_n` in the family with
`max_{s ∈ T_St} ‖π_{D_n J}(s) − I‖₂ → 0`.  Each chart is an exact
representation of `A₈`, so each `n` gives an honest homomorphism
`P̄ → U(20160 k_n)`; passing to the tracial matrix ultraproduct and using that
every `s ∈ T_St` has defect `→ 0` gives a homomorphism

```
Ψ : E = P̄/⟨⟨T_St⟩⟩ ⟶ U(∏_ω M_{20160 k_n}) .
```

`Ψ` is nontrivial: chart 1 stays the regular representation, so for a
noncommuting pair `x, y` of first-chart elements
`‖[Ψ(x), Ψ(y)] − I‖₂ = √2` exactly at every `n`.  By
`atlas-relator-central-sufficiency`, `E` is a perfect central extension of the
nonabelian simple `Q`, hence quasisimple, so every proper normal subgroup of
`E` is central; `ker Ψ` is proper, so `ker Ψ ≤ Z(E)`.  But `(*)` gives
`π_{D_n J}(c) = I` **exactly at every `n`**, so `c ∈ ker Ψ ≤ Z(E)`.  The image
of `Z(E)` in `Q` is central in `Q` (the map is onto) and `Z(Q) = 1`, so `c`
would map to `1` in `Q` — contradicting the normal-form computation.  ∎

**What it kills and what it does not.**  It kills the entire index-15
stabilizer-coset lane: no multiplicity, no optimizer, and no arbitrarily
complicated `U(15k)` block can rescue it, so Stage 1 and its planned exact
Stage-1b engine should not be run.  It does **not** touch the unrestricted
criterion: a witness may still exist among `U_n ∈ U(20160 k_n)` that do not
asymptotically preserve an exact nontrivial first-chart stabilizer commutant.

**The reusable form.**  The argument never used the shape of `D` beyond one
exact commutation.  In general: *any* structured atlas family that forces an
exact relation on `P̄` whose image in `Q` is nontrivial is globally excluded,
at every multiplicity, by quasisimplicity of `E` plus `Z(Q) = 1`.  Screening a
proposed ansatz for accidentally-forced relations — and evaluating them in the
Leavitt normal form — is therefore a cheap first test that should precede any
optimization spend.

## (f) What the audit did not move

The affirmative side of Q3.4 is untouched, and the audit says so: proving one
Leavitt candidate nonhyperlinear would be a landmark (no nonhyperlinear
discrete group is known) but would **not** answer Pestov "Yes" — that needs a
general conversion of hyperlinear approximations into sofic ones.  The graph
already encodes exactly this asymmetry on `q3-4-resolved`, and the audit
independently reproduces the same reading of the fork: the fork theorem is
established, and selecting its branch is what has not been done.
