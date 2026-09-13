# Strict comparison with bounded rank density kills every support gap (2026-09-12)

Lane `tw-support-gap-crux`.

**Task.** Decide `comparison-forces-tracial-support-projections`: prove that
comparison forces near projections under every positive contraction with trace
at least its trace, or build an algebra with strict comparison and a positive
support gap `γ_A(a) > 0`.

**Outcome.**
1. **Theorem 1 (settled, positive).** Take a unital simple algebra with strict
   comparison of positive elements and bounded rank density (RD_b). Then every
   support gap vanishes, i.e. it has tracial support projections (TSP). No
   nuclearity, dimension or Gamma hypothesis is used.
2. **Corollary 2.** The Toms–Winter conjecture holds among unital, simple,
   separable, nuclear, non-elementary algebras with tracially locally finite
   nuclear dimension and RD_b. Strict comparison there already gives
   Z-stability.
3. **What stays open.** The claim as stated assumes only projection comparison
   in the tracial ultrapower (PC), not strict comparison. Its PC-only form is
   untouched: the proof below moves a projection under a non-projection, which
   PC cannot do.
4. **Counterexample side.** A support-gap certificate against Gamma can never
   coexist with strict comparison and RD_b. So a Toms–Winter counterexample must
   fail RD_b, or fail tracially locally finite nuclear dimension.

Notation follows `research/artifacts/tw-invisible-gamma-support-gap-2026-09-12.md`,
Sections 0–1 (`γ_A`, TSP, PC, PD, RD_b, limit traces, Fact 0).

## 1. Theorem 1

**Setting.**
- `A` is a unital simple C*-algebra with `T(A) ≠ ∅`.
- Traces on `M_k(A)` are unnormalized, `τ ⊗ Tr_k`, and `d_τ(x) = lim_n τ(x^{1/n})`.
- **Strict comparison.** For all `m` and all `x, y ∈ M_m(A)_+`: if
  `d_τ(x) < d_τ(y)` for every `τ ∈ T(A)`, then `x ≾ y` (Cuntz subequivalence).
- **RD_b.** For every `k`, every continuous affine `f: T(A) → [0,k]` and every
  `η > 0`, there is a positive contraction `q ∈ M_k(A)` with
  `sup_τ |τ(q) − f(τ)| < η` and `sup_τ τ(q − q²) < η`.

**Theorem 1.** If `A` has strict comparison and RD_b, then `γ_A(a) = 0` for every
`k` and every positive contraction `a ∈ M_k(A)`. Equivalently (Lemma A of the
support-gap artifact), `A` has TSP.

**Standard inputs.**
- **(R) Rørdam's lemma** (Kirchberg–Rørdam, Adv. Math. 2002, Lemma 2.2; not
  re-read). If `x, y ≥ 0` and `‖x − y‖ < δ`, there is a contraction `d` with
  `(x − δ)_+ = d y d*`.
- **(T) Trace identity.** For every `c` and every tracial state `τ`,
  `τ((c*c)^n) = τ((cc*)^n)` for `n ≥ 1`. Uniform approximation by polynomials
  without constant term gives `τ(h(c*c)) = τ(h(cc*))` for every continuous `h`
  with `h(0) = 0`.
- **(H) Hereditary pieces.** `her_A(a) = closure(a M_k(A) a) = closure(a^{1/2} M_k(A) a^{1/2})`.
  It is a C*-algebra, so `h(e) ∈ her_A(a)` whenever `e ∈ her_A(a)_+` and `h(0) = 0`.

*Proof.*

*Step 0 (constants).*
- If `a = 0`, take `b = 0`.
- Otherwise put `c := min_τ τ(a)`. The map `τ ↦ τ(a)` is continuous on the
  compact set `T(A)`, and every tracial state of a unital simple algebra is
  faithful, so `c > 0`. Also `c ≤ k`.
- Fix `ε ∈ (0, 1/4)`. Put `δ := ε/4` and `η := εcδ/8`.

*Step 1 (a near projection of the right profile).*
- `f(τ) := (1 − ε) τ(a)` is continuous affine with values in `[0, k]`.
- RD_b gives a positive contraction `q ∈ M_k(A)` with `|τ(q) − f(τ)| < η` and
  `τ(q − q²) < η` for all `τ`.
- Write `μ_τ` for the spectral measure of `q` under `τ ⊗ Tr_k`. It has mass `k`.

*Step 2 (the rank of `(q − δ)_+` is strictly below that of `a`).*
- On `[δ, 1 − δ]` we have `t − t² ≥ δ(1 − δ) ≥ δ/2`, so `μ_τ((δ, 1−δ)) ≤ 2η/δ`.
- `μ_τ([1−δ, 1]) ≤ τ(q)/(1 − δ)`.
- So `d_τ((q − δ)_+) = μ_τ((δ, 1]) ≤ 2η/δ + ((1−ε)τ(a) + η)/(1 − δ)`.
- Since `δ = ε/4`, `(1 − ε)/(1 − ε/4) ≤ 1 − 3ε/4`. Also `η/(1−δ) ≤ 2η ≤ 2η/δ`.
- Hence `d_τ((q − δ)_+) ≤ τ(a) − (3ε/4) c + 4η/δ = τ(a) − (3ε/4)c + εc/2 < τ(a)`.
- Since `a` is a contraction, `a^{1/n} ≥ a`, so `d_τ(a) ≥ τ(a)`.
- Therefore `d_τ((q − δ)_+) < d_τ(a)` for every `τ ∈ T(A)`.

*Step 3 (move it under `a`).*
- Strict comparison gives `(q − δ)_+ ≾ a`. Choose `r ∈ M_k(A)` with
  `‖(q − δ)_+ − r a r*‖ < δ`.
- By (R) there is a contraction `d ∈ M_k(A)` with
  `d (r a r*) d* = ((q − δ)_+ − δ)_+ = (q − 2δ)_+`.
- Put `c_0 := d r a^{1/2}`. Then `c_0 c_0* = (q − 2δ)_+`, and
  `c_0* c_0 = a^{1/2} r* d* d r a^{1/2} ∈ her_A(a)` by (H).

*Step 4 (the near projection under `a`).*
- Let `ψ(s) := min(1, s/(1 − 4δ))` for `s ≥ 0`, so `ψ(0) = 0`, and put
  `b := ψ(c_0* c_0)`. By (H), `b` is a positive contraction in `her_A(a)`.
- Put `φ(t) := ψ((t − 2δ)_+)`. Then `ψ(c_0 c_0*) = φ(q)`, and by (T),
  `τ(b) = τ(φ(q))` and `τ(b − b²) = τ(φ(q) − φ(q)²)` for every `τ`.
- **Defect.** `φ(t) ∈ (0,1)` only for `t ∈ (2δ, 1 − 2δ)`, where
  `t − t² ≥ 2δ(1 − 2δ) ≥ δ`. So `φ − φ² ≤ (1/4)·1_(2δ,1−2δ)`, and
  `τ(b − b²) ≤ μ_τ((2δ, 1−2δ))/4 ≤ η/(4δ) = εc/32 ≤ εk`.
- **Trace.** `φ(t) ≥ t − 4δ` on `[0,1]`: it is `0 ≥ t − 4δ` for `t ≤ 2δ`,
  `(t − 2δ)/(1 − 4δ) ≥ t − 2δ` on `[2δ, 1−2δ]`, and `1 ≥ t` above. So
  `τ(b) ≥ τ(q) − 4δk ≥ (1 − ε)τ(a) − η − εk ≥ τ(a) − 3εk`.
- Hence `γ_A(a) ≤ 3εk` for every `ε ∈ (0, 1/4)`, so `γ_A(a) = 0`. ∎

**Remarks.**
- **What was used.** Simplicity is used only for faithfulness of traces (`c > 0`).
  RD_b is used once, at the matrix size of `a`, for the single profile
  `(1 − ε)τ(a)`. Strict comparison is used once, against `a` itself.
- **Why PC does not suffice.** Step 3 compares the near projection with the
  non-projection `a`, and produces a projection under `a` through
  `c_0*c_0 ~ c_0c_0*`. PC compares projections only; the dilation trick of the
  support-gap artifact (Section 5) carries no information about `a`.
- **Sanity check.** `C([0,1])` with `a = id` has `γ(a) = 1/4`, and it is not
  simple. The argument fails there at Step 0 (the trace at the point 0 kills
  `a`) and at strict comparison.

## 2. Corollary 2: Toms–Winter on the tlfnd + RD_b locus

**Corollary 2.** Let `A` be a unital, simple, separable, nuclear, non-elementary
C*-algebra with `T(A) ≠ ∅`, tracially locally finite nuclear dimension (Vaccaro,
arXiv:2604.24682, Definition 1.5) and RD_b. If `A` has strict comparison of
positive elements, then `A` is Z-stable and has finite nuclear dimension.

*Proof.* Every step is a claim already established on main, except TSP.
1. **PC.** Strict comparison gives comparison of projections by limit traces in
   every `M_k(A^U)` (`strict-comparison-compares-ultrapower-projections`,
   reviewer PASS).
2. **PD.** PC and RD_b divide every projection of every `M_k(A^U)`
   (`ultrapower-comparison-with-rank-density-divides-projections`).
3. **TSP.** Theorem 1 (`strict-comparison-with-rank-density-gives-support-projections`).
4. **Gamma.** Under tracially locally finite nuclear dimension, TSP and PD give
   uniform property Gamma
   (`uniform-gamma-iff-tracial-support-projections-and-division`, part (b)).
5. **Z-stability.** Uniform Gamma together with strict comparison gives
   Z-stability and finite nuclear dimension (CETW arXiv:1912.04207 Theorem A;
   `uniform-gamma-algebras-satisfy-toms-winter`). ∎

**Scope.**
- Among these algebras, strict comparison ⟹ Z-stability. The converse is
  standard (Rørdam). So on this locus Toms–Winter holds in the unital direction
  that was open.
- With norm locally finite nuclear dimension this was already known, through
  `rank-density-and-strict-comparison-give-purity` and Winter's theorem. The
  new part of the locus is tracially-but-not-norm locally finite nuclear
  dimension with RD_b.

## 3. Relation to the literature (bounded, not a priority search)

- **Vaccaro, arXiv:2604.24682, Theorem B** (MSI text copy, lines 89–91):
  "Let A be a separable, simple, unital, non-elementary, stably finite
  C∗-algebra with stable rank one and tracially locally finite nuclear
  dimension. Then A has uniform property Γ."
- **Lin's theorem on main** (`strict-comparison-rank-surjectivity-forces-sr1`):
  strict comparison plus a surjective rank map forces stable rank one.
- Combined with CETW, these give Toms–Winter on the locus "tracially locally
  finite nuclear dimension plus surjective rank map". Corollary 2 replaces
  surjectivity of the rank map by RD_b. That is approximate profile selection
  by near projections at bounded matrix size.
- **Not checked.** Whether RD_b implies, or follows from, surjectivity of the
  rank map under strict comparison.
- **Credit.** Theorem 1 is an elementary combination of Rørdam's lemma, the
  trace identity for `c*c` and `cc*`, and the spectral estimates of the
  support-gap artifact. No novelty is asserted for Theorem 1 or Corollary 2.

## 4. Effect on the graph

- **New, established:**
  - `strict-comparison-with-rank-density-gives-support-projections`, via route
    `strict-comparison-rank-density-support-projections-proof` (direct proof,
    Section 1);
  - `toms-winter-holds-on-tlfnd-rank-density-locus`, via route
    `toms-winter-tlfnd-rank-density-locus-proof`, which requires the five
    claims of Corollary 2.
- **Unchanged and open:**
  - `comparison-forces-tracial-support-projections` (PC-only hypothesis), with
    an Attempts bullet recording the strict-comparison case;
  - `tracial-comparison-gives-gamma-on-lfnd-rank-density-locus`;
  - `gamma-failure-invisible-to-projection-comparison`;
  - `stw99-problem-xviii-toms-winter-conjecture`.

## Trust surfaces

- The proof of Theorem 1 is self-contained and elementary. Rørdam's lemma and
  the trace identity are standard and were not re-read from source.
- Corollary 2 rests on the five established claims listed. They have their own
  imports: CETW Theorem 4.6 and Theorem A, and Vaccaro Proposition 1.6.
- Not independently reviewed, and nothing is in Lean.
