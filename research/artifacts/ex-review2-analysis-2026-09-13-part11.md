# EX review wave 2, part 11: census of the wave-2 operator-algebra lanes (2026-09-13)

Lane `ex-verify2-analysis`. Main added fourteen wave-2 lanes to this lane's scope. Verdicts for this census go in later
part files, and each is indexed in `ex-review2-analysis-2026-09-13.md`.

**Lanes.**
- ex2-uct-unit-class-cohomology, ex2-uct-dual-action-transfer, ex2-uct-z2-strongly-approx-inner, ex2-uct-norm-functor;
- ex2-bk-relative-lemma-b;
- ex2-rr0-clopen-type;
- ex2-tw-unsplittable-tails, ex2-tw-hilbert-cube-boundary;
- ex2-rank-monotone-rounding;
- ex2-unitary-class-five;
- ex2-k1-defect-ideal;
- ex2-bc-cylinder-comparison;
- ex2-cubic-ihara-bass;
- ex2-nh-deligne-sector-floor.

## 11.0 Method

The method is the part 0 method, run at tip `59ea57d883`. It is a structural recomputation, not `cairn check`.
- **Nodes.** `state/landed.log` has 84 landings by these lanes, touching 86 claims.
- **Established.** Routes are gathered into every lane claim and, recursively, into missing prerequisites, over five
  levels (139 claims, 118 routes). The FRONTIER statuses are the seed, and the route rule is iterated eight times.
  Block-list parsing uses the corrected END clause.
- **Reviewed.** An id counts as reviewed if it occurs on a PASS line of some `research/artifacts/ex-review*.md` at that
  tip.
- **Result.** 39 claims are established structurally with no PASS.
  - Six of them are ex2-rr0-clopen-type claims, covered by part 10, which landed after the tip.
  - The ex2-tw-unsplittable-tails claims already had PASS in part 9.
  - **33 remain.**

**Roots touched by these lanes.**
- `nontrivial-w-star-bundle-with-r-fibres-exists` is now established, through the Pauli tower. PASS in part 9.
- `stw99-problem-lxi-properly-infinite-k1-injective` and `stw99-problem-xxix-rr0-dichotomy` stay open.

## 11.1 The 33 remaining claims, in review order

| priority | lane | claim |
|---|---|---|
| A (LXI chain) | k1-defect-ideal | `o2-quotient-extension-ideal-k1-injective-iff-algebra` |
| A | k1-defect-ideal | `toeplitz-defect-ideal-connected-iff-extension-k1-injective` |
| A | k1-defect-ideal | `nonzero-fibre-projection-full-under-weak-omega-comparison` |
| B (UCT dynamics) | uct-z2-strongly-approx-inner | `bemsw-outer-z2-kirchberg-rokhlin-dimension-at-most-one` |
| B | uct-z2-strongly-approx-inner | `ghs-z2-commuting-rokhlin-dimension-one-dual-sai` |
| B | uct-z2-strongly-approx-inner | `z2-o2-implementing-cocycle-classes-are-path-components` |
| B | uct-z2-strongly-approx-inner | `z2-odd-commutator-below-half-forces-commuting-towers` |
| B | uct-unit-class-cohomology | `gabe-szabo-asymptotic-coboundary-kk-criterion` |
| B | uct-unit-class-cohomology | `zp-o2-contractible-crossed-product-only-coboundaries` |
| B | uct-unit-class-cohomology | `zp-o2-generator-kk-class-is-twisted-asymptotic-innerness` |
| B | uct-dual-action-transfer | `o2-central-sequence-k-theory-bi-cyclotomic-transfer` |
| B | uct-dual-action-transfer | `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion` |
| B | uct-norm-functor | `kk-tensor-power-norm-functor-to-kk-zp` |
| B | uct-norm-functor | `o2-tensor-power-shift-is-rokhlin` |
| C (class five) | unitary-class-five | `lambda-mod-m-bordism-splits-as-string-bordism-in-a-range` |
| C | unitary-class-five | `rank-three-stable-fivefold-commutator-two-primary` |
| C | unitary-class-five | `spin-m-trapping-factors-through-string-bordism` |
| C | unitary-class-five | `top-cell-commutator-class-is-product-of-adjoint-j-invariants` |
| D | tw-hilbert-cube-boundary | `bauer-strict-comparison-unit-divides-iff-atomless-element` |
| D | tw-hilbert-cube-boundary | `bauer-unit-division-defect-uniform-criterion` |
| D | tw-hilbert-cube-boundary | `square-atomless-measure-family-forces-dirac-pushforward` |
| D | tw-hilbert-cube-boundary | `zero-dimensional-atomless-diagonal-divides-unit` |
| D | rank-monotone-rounding | `toms-block-diagonal-sharpening-has-fuzz-persistence` |
| D | rank-monotone-rounding | `toms-line-subalgebra-has-no-nonconstant-continuous-rank` |
| D | rank-monotone-rounding | `toms-monotone-block-rounding-obeys-a-miranda-granularity-bound` |
| D | rank-monotone-rounding | `toms-rank-bookkeeping-admits-monotone-realizer-profiles` |
| D | rank-monotone-rounding | `toms-simple-algebra-has-no-block-diagonal-rank-realizer` |
| D | bk-relative-lemma-b | `bk-relative-boundary-descends-or-is-positively-detected` |
| E | cubic-ihara-bass | `cubic-division-congruence-outliers-delocalise-at-log-scale` |
| E | cubic-ihara-bass | `cubic-division-ihara-traces-count-roots-mod-p` |
| E | cubic-ihara-bass | `free-group-ihara-bass-outlier-trace-criterion` |
| E | nh-deligne-sector-floor | `deligne-monomial-cover-models-have-a-detecting-cycle-floor` |
| E | bc-cylinder-comparison | `bernoulli-defects-vanish-along-bcc-subgroup-tubes` |

**Why this order.**
- A feeds LXI.
- B bears on detection at Z/p and on Barlak--Li Remark 4.14(2).
- C is class five of unitary component groups.
- D is Toms--Winter and rank-problem machinery.
- E covers strong convergence, Deligne covers and Baum--Connes.
