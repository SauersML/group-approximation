# EX review, wave 2: operator algebras, K-theory and Hilbert--Schmidt analysis (2026-09-13)

Lane `ex-verify2-analysis`, second-wave adversarial verifier of the EX swarm. Start tip `7d41d1a16`.
The first wave is `ex-review-analysis-2026-09-12.md` and its part files (lane `ex-verify-analysis`).
Long sections go to part files `ex-review2-analysis-2026-09-13-part<N>.md`, indexed at the end.

## 0. Scope and method

**Lanes.**
- rank-toms-b-obstruct, rank-toms-b-construct, rank-problem-villadsen, rank-problem-lix.
- tw-projection-starved-bundle, tw-rotation-gluing, toms-winter.
- uct-detection-prove, uct-detection-phantom, uct, bk-glued-uct, blackadar-kirchberg.
- rr0-tarski-ideals, rr0-dichotomy.
- k1-halving-homotopy, k1-properly-infinite.
- unitary-string-trapping, unitary-higher-brackets.
- bc-module-monster, bc-module-exactness, bc-measured-coefficient.
- cubic-division-strong-convergence, sl3z-purely-matricial, mf-kazhdan-cstar.
- hs-masa-lift-positive, hs-masa-lift-counter, nh-deligne-hs, hs-instability-extension.

**Verdicts.**
- **PASS**: re-derived independently; the statement, hypotheses and citations match.
- **GAP**: the statement may be true, but the written argument or its scope does not prove it as stated.
- **FAIL**: the statement is false as written, or the argument is broken beyond local repair.
- A wording note with no verdict change is labelled as such.

**Census method.** This is a structural recomputation, not `cairn check`.
- **Nodes.** `state/landed.log` has 164 landings by these lanes. They touch 367 node files; 363 are on main
  at the start tip (197 claims and 166 routes).
- **Established.** A claim counts as established if some route into it is not named under `invalidates:`
  and every prerequisite of that route is established.
  - The seed set is the ESTABLISHED statuses of `research/FRONTIER.md` at `5cc8cb507`, generated from
    `cairn check` at `d20a93228` (00:29 CDT).
  - The rule was then iterated eight times over every route into a lane claim, and every route into a
    prerequisite missing from the seed set.
- **Reviewed.** A claim counts as reviewed if its id occurs on a line containing PASS in some
  `research/artifacts/ex-review-*.md` file at the tip.
- **Result.** 86 claims are established structurally and have no PASS.

**Already reviewed in priority (c)**, all PASS in `ex-review-analysis-2026-09-12-part4.md`:
- `toms-schubert-algebra-fails-o6-plus` (Theorem A of ex-rank-problem-lix);
- `o6-plus-forces-tracial-equivalence-of-equal-trace-projections`;
- `toms-schubert-algebra-has-no-small-joins`.

**Roots.** Checked structurally at the start tip; the leaves of these chains were not re-derived here.
- `simple-cstar-unitary-components-class-four` flips to established, through
  `class-four-via-lambda-mod-eight-trapping-tower`. It is a question built in this repository, not a
  named external problem. Its review is priority (a).
- These stay open, because every route into them needs an open prerequisite:
  - `stw23-rank-problem-counterexample-exists`, which needs `toms-schubert-algebra-misses-a-rank`.
    That in turn needs the open `toms-schubert-algebra-continuous-ranks-are-constant`.
  - `stw18-strict-comparison-non-z-stable-algebra-exists` and `stw27-strict-comparison-non-pure-algebra-exists`.
  - `toms-winter-holds-on-bauer-tlfnd-locus`, `stw99-problem-ii-nuclear-uct`, `stw99-problem-xxix-rr0-dichotomy`
    and `stw99-problem-lxi-properly-infinite-k1-injective`.
  - `infinite-kazhdan-group-with-mf-reduced-cstar`, whose three routes need `sl3z-purely-matricial-field`,
    `cubic-division-lattice-purely-matricial-field` or `kt-double-reduced-cstar-is-mf`, all open.
  - The Deligne chain into `non-hyperlinear-group`: `deligne-stable-triple-cover-is-not-hyperlinear` needs
    `deligne-central-mark-hs-collapse`, which needs `maslov-mod3-projective-defect-gap`, which is open.

## 1. Census: established, no PASS (86 claims)

Priorities from the brief:
- (a) the class-four chain and its neighbours;
- (b) the tw-rotation-gluing construction;
- (c) the rank-obstruct claims;
- (d) UCT detection;
- (e) everything else.

| claim | lane | priority |
|---|---|---|
| `ah-unitary-component-kernel-is-locally-finite` | unitary-higher-brackets | a |
| `rank-two-spin-trapping-blind-to-depth-three-brackets` | unitary-higher-brackets | a |
| `rank-two-trapping-blind-to-depth-four-brackets` | unitary-higher-brackets | a |
| `spin-trapping-blind-to-fourfold-commutators-in-every-rank` | unitary-higher-brackets | a |
| `eta-cubed-commutator-has-nonzero-lambda-mod-eight-class` | unitary-string-trapping | a |
| `eta-cubed-survives-in-lambda-mod-eight-bordism` | unitary-string-trapping | a |
| `nested-commutators-pull-ko-of-unitary-groups-into-eta-powers` | unitary-string-trapping | a |
| `quaternionic-flag-trapping-steps-are-never-string` | unitary-string-trapping | a |
| `quaternionic-grassmannian-trapping-defect-is-rank` | unitary-string-trapping | a |
| `rank-two-trapping-blind-to-fivefold-sphere-commutators` | unitary-string-trapping | a |
| `simple-ah-algebra-with-class-four-component-group` | unitary-string-trapping | a |
| `simple-cstar-unitary-components-class-four` | unitary-string-trapping | a |
| `trapped-lambda-mod-eight-class-over-seed-factor` | unitary-string-trapping | a |
| `unitary-word-transfer-to-simple-ah-via-trapping` | unitary-string-trapping | a |
| `bauer-c-space-strict-comparison-divides-unit` | tw-rotation-gluing | b |
| `bauer-c-space-strict-comparison-pure-and-z-stable` | tw-rotation-gluing | b |
| `bauer-strict-comparison-unit-division-is-local` | tw-rotation-gluing | b |
| `bauer-unit-division-iff-summable-local-division` | tw-rotation-gluing | b |
| `bauer-unit-division-metric-order-criterion` | tw-rotation-gluing | b |
| `toms-diagonal-quotient-has-nonconstant-continuous-ranks` | rank-toms-b-obstruct | c |
| `toms-twisted-swap-pairs-are-totally-degeneracy-forcing` | rank-toms-b-obstruct | c |
| `gabe-szabo-unital-uniqueness-theorem` | uct-detection-phantom | d |
| `kohler-uct-for-zp-equivariant-bootstrap` | uct-detection-phantom | d |
| `meyer-little-invariant-detects-zero-in-zp-bootstrap` | uct-detection-phantom | d |
| `mn-cyclic-restrictions-detect-equivariant-bootstrap` | uct-detection-phantom | d |
| `zp-detection-equals-meyer-nadareishvili-sufficiency` | uct-detection-phantom | d |
| `zp-o2-action-kkg-trivial-iff-invariant-asymptotic-inner` | uct-detection-phantom | d |
| `zp-restriction-trivial-splits-cellular-plus-phantom` | uct-detection-phantom | d |
| `o2-contractible-crossed-product-inner-half-flip-mcduff` | uct-detection-prove | d |
| `o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences` | uct-detection-prove | d |
| `outer-actions-on-o2-kk-g-contractible-iff-rokhlin` | uct-detection-prove | d |
| `zp-detection-iff-bootstrap-sufficiency-and-kk-g-generation` | uct-detection-prove | d |
| `bernoulli-assembly-injective-beyond-the-host` | bc-measured-coefficient | e |
| `bernoulli-bc-splits-into-host-and-cylinder-comparison` | bc-measured-coefficient | e |
| `bernoulli-shift-weak-k-equivalence-and-going-down` | bc-measured-coefficient | e |
| `module-defect-needs-non-k-exact-host` | bc-module-monster | e |
| `monster-bc-detector-lives-on-a-proper-orbit-ideal` | bc-module-monster | e |
| `osajda-monster-hosts-for-bc-module-route` | bc-module-monster | e |
| `bk-projection-generated-ideals-with-uct-quotients-force-qd` | bk-glued-uct | e |
| `bk-radical-projection-quotients-are-toeplitz-infinite` | bk-glued-uct | e |
| `bk-radical-traces-vanishing-on-boundary-are-zero` | bk-glued-uct | e |
| `bk-uct-counterexample-radical-not-projection-generated` | bk-glued-uct | e |
| `moutzouris-k0-killing-is-local` | bk-glued-uct | e |
| `moutzouris-singular-subgroup-has-vanishing-trace` | bk-glued-uct | e |
| `brown-dadarlat-ext-trivial-class-gives-qd-extension` | blackadar-kirchberg | e |
| `gabe-no-compact-open-prim-embeds-in-cone` | blackadar-kirchberg | e |
| `congruence-sc-fails-along-levels-with-recurring-divisor` | cubic-division-strong-convergence | e |
| `cubic-division-congruence-sc-descends-to-thin-subgroups` | cubic-division-strong-convergence | e |
| `cubic-division-congruence-sc-forces-asymptotic-laplace-gap` | cubic-division-strong-convergence | e |
| `kt-wreath-models-never-round-on-the-vertex` | hs-instability-extension | e |
| `o2-free-range-projection-homotopy-iff-halving` | k1-halving-homotopy | e |
| `o2-ideal-finite-nucdim-counterexample-unital-quotients` | k1-halving-homotopy | e |
| `o2-ideal-projection-unit-witness-fails-cancellation` | k1-halving-homotopy | e |
| `self-similar-hilbert-cx-module-has-unit-section` | k1-halving-homotopy | e |
| `bdl-deligne-type-two-norm-inapproximability` | nh-deligne-hs | e |
| `blsw-real-lattice-frobenius-stability` | nh-deligne-hs | e |
| `deligne-covers-of-sp2g-z-have-finite-residual-2z` | nh-deligne-hs | e |
| `cuntz-sups-with-continuous-rank-converge-uniformly` | rank-toms-b-construct | e |
| `ara-goodearl-tame-refinement-monoids-separative` | rr0-dichotomy | e |
| `opr-cfp-rr0-dichotomy` | rr0-dichotomy | e |
| `opr-mixed-simple-refinement-monoid` | rr0-dichotomy | e |
| `opr-properly-infinite-multiple-splits` | rr0-dichotomy | e |
| `rainone-type-semigroup-crossed-product-dichotomy` | rr0-dichotomy | e |
| `rordam-mixed-examples-not-real-rank-zero` | rr0-dichotomy | e |
| `af-crossed-product-counterexample-normal-form` | rr0-tarski-ideals | e |
| `af-k0-order-divisible-iff-no-elementary-subquotient` | rr0-tarski-ideals | e |
| `coinvariant-tarski-lemma-minimal-nowhere-scattered` | rr0-tarski-ideals | e |
| `dimension-group-divisible-iff-no-integer-subquotient` | rr0-tarski-ideals | e |
| `minimal-normal-cyclic-subgroup-cantor-dichotomy` | rr0-tarski-ideals | e |
| `nowhere-scattered-af-crossed-products-dichotomy` | rr0-tarski-ideals | e |
| `nowhere-scattered-af-integer-crossed-products-dichotomy` | rr0-tarski-ideals | e |
| `rr0-sr1-coefficient-crossed-products-dichotomy` | rr0-tarski-ideals | e |
| `smoothing-normal-subgroup-cantor-dichotomy` | rr0-tarski-ideals | e |
| `affine-sl2z-purely-matricial-field` | sl3z-purely-matricial | e |
| `mdls-obstruction-is-affine-mechanism-plus-level-matching` | sl3z-purely-matricial | e |
| `pmf-permanence-amenable-kernel-without-exactness` | sl3z-purely-matricial | e |
| `sl3z-pmf-iff-affine-kazhdan-group-pmf` | sl3z-purely-matricial | e |
| `sl3z-prime-level-invariant-witnesses-are-complete` | sl3z-purely-matricial | e |
| `sl3z-prime-level-sc-forces-congruence-sc-for-sl2z` | sl3z-purely-matricial | e |
| `sl3z-prime-level-sc-needs-cubic-chebotarev-primes` | sl3z-purely-matricial | e |
| `block-balanced-towers-have-central-halving` | tw-projection-starved-bundle | e |
| `central-halving-trivializes-every-closed-bauer-face-bundle` | tw-projection-starved-bundle | e |
| `closed-extreme-trace-sets-give-r-fibre-w-star-bundles` | tw-projection-starved-bundle | e |
| `hopf-doubling-tower-has-no-m2-but-divides-unit-tracially` | tw-projection-starved-bundle | e |
| `tensor-tower-bundle-trivial-iff-tails-softly-split` | tw-projection-starved-bundle | e |
| `toms-no-gamma-algebra-is-trivial-on-closed-bauer-faces` | tw-projection-starved-bundle | e |

## 2. Verdicts

Filled in as each part lands.

| claim | lane | verdict | part |
|---|---|---|---|
| `eta-cubed-survives-in-lambda-mod-eight-bordism` | unitary-string-trapping | PASS | 1 §1.2 |
| `trapped-lambda-mod-eight-class-over-seed-factor` | unitary-string-trapping | PASS, SU(2)/U(2) note | 1 §1.3 |
| `eta-cubed-commutator-has-nonzero-lambda-mod-eight-class` | unitary-string-trapping | PASS | 1 §1.4 |
| `quaternionic-grassmannian-trapping-defect-is-rank` | unitary-string-trapping | PASS | 1 §1.5 |
| `simple-ah-algebra-with-class-four-component-group` | unitary-string-trapping | PASS | 1 §1.6 |
| `simple-cstar-unitary-components-class-four` (root, flips) | unitary-string-trapping | PASS | 1 §1.1, §1.6 |
| `unitary-word-transfer-to-simple-ah-via-trapping` | unitary-string-trapping | PASS | 1 §1.7 |
| route `nonnilpotent-via-glued-trapping-towers` | unitary-string-trapping | PASS, conditional, does not fire | 1 §1.8 |
| `rank-two-trapping-blind-to-fivefold-sphere-commutators` | unitary-string-trapping | PASS | 1 §1.9 |
| `nested-commutators-pull-ko-of-unitary-groups-into-eta-powers` | unitary-string-trapping | PASS | 1 §1.10 |
| `quaternionic-flag-trapping-steps-are-never-string` | unitary-string-trapping | PASS | 1 §1.11 |
| `rank-two-spin-trapping-blind-to-depth-three-brackets` | unitary-higher-brackets | PASS, ABP recalled | 1 §1.12 |
| `rank-two-trapping-blind-to-depth-four-brackets` | unitary-higher-brackets | PASS | 1 §1.12 |
| `spin-trapping-blind-to-fourfold-commutators-in-every-rank` | unitary-higher-brackets | PASS, ABP and Wood recalled | 1 §1.12 |
| `ah-unitary-component-kernel-is-locally-finite` | unitary-higher-brackets | PASS | 8 §8.1 |
| `bauer-c-space-strict-comparison-divides-unit` (Theorem A; Lemma 3 of part 1, Section 3 of part 2) | tw-rotation-gluing | PASS, wording note | 2 §2.2, §2.3 |
| `bauer-c-space-strict-comparison-pure-and-z-stable` | tw-rotation-gluing | PASS | 2 §2.4 |
| `bauer-strict-comparison-unit-division-is-local` | tw-rotation-gluing | PASS | 2 §2.5 |
| `bauer-unit-division-iff-summable-local-division` (Theorem E) | tw-rotation-gluing | PASS | 2 §2.6 |
| `bauer-unit-division-metric-order-criterion` (Lemma 8.1 of part 4) | tw-rotation-gluing | PASS, wording note | 2 §2.7 |
| `toms-diagonal-quotient-has-nonconstant-continuous-ranks` | rank-toms-b-obstruct | PASS | 2 §2.8 |
| `toms-twisted-swap-pairs-are-totally-degeneracy-forcing` | rank-toms-b-obstruct | PASS, wording note | 2 §2.9 |
| `gabe-szabo-unital-uniqueness-theorem` | uct-detection-phantom | PASS, quotes verbatim | 3 §3.2 |
| `kohler-uct-for-zp-equivariant-bootstrap` | uct-detection-phantom | PASS as import | 3 §3.2 |
| `meyer-little-invariant-detects-zero-in-zp-bootstrap` | uct-detection-phantom | PASS, quote verbatim | 3 §3.2 |
| `mn-cyclic-restrictions-detect-equivariant-bootstrap` | uct-detection-phantom | PASS | 3 §3.2 |
| `zp-detection-equals-meyer-nadareishvili-sufficiency` | uct-detection-phantom | PASS | 3 §3.3 |
| `zp-restriction-trivial-splits-cellular-plus-phantom` | uct-detection-phantom | PASS | 3 §3.4 |
| `zp-o2-action-kkg-trivial-iff-invariant-asymptotic-inner` | uct-detection-phantom | PASS | 3 §3.5 |
| `outer-actions-on-o2-kk-g-contractible-iff-rokhlin` | uct-detection-prove | PASS | 3 §3.6 |
| `o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences` | uct-detection-prove | PASS | 3 §3.7 |
| `o2-contractible-crossed-product-inner-half-flip-mcduff` | uct-detection-prove | PASS | 3 §3.8 |
| `zp-detection-iff-bootstrap-sufficiency-and-kk-g-generation` | uct-detection-prove | PASS after graph fix `d16d59955a` | 3 §3.1, §3.9 |
| `ara-goodearl-tame-refinement-monoids-separative` | rr0-dichotomy | PASS, quote verbatim | 4 §4.1 |
| `opr-cfp-rr0-dichotomy` | rr0-dichotomy | PASS, quote verbatim | 4 §4.1 |
| `opr-mixed-simple-refinement-monoid` | rr0-dichotomy | PASS, quote verbatim | 4 §4.1 |
| `opr-properly-infinite-multiple-splits` | rr0-dichotomy | PASS, quote verbatim | 4 §4.1 |
| `rainone-type-semigroup-crossed-product-dichotomy` | rr0-dichotomy | PASS as import | 4 §4.1 |
| `rordam-mixed-examples-not-real-rank-zero` | rr0-dichotomy | PASS as import, not re-read | 4 §4.1 |
| `coinvariant-tarski-lemma-minimal-nowhere-scattered` | rr0-tarski-ideals | PASS | 4 §4.2 |
| `af-k0-order-divisible-iff-no-elementary-subquotient` | rr0-tarski-ideals | PASS | 4 §4.3 |
| `dimension-group-divisible-iff-no-integer-subquotient` | rr0-tarski-ideals | PASS | 4 §4.4 |
| `nowhere-scattered-af-crossed-products-dichotomy` | rr0-tarski-ideals | PASS | 4 §4.5 |
| `nowhere-scattered-af-integer-crossed-products-dichotomy` | rr0-tarski-ideals | PASS, note | 4 §4.6 |
| `rr0-sr1-coefficient-crossed-products-dichotomy` | rr0-tarski-ideals | PASS | 4 §4.7 |
| `minimal-normal-cyclic-subgroup-cantor-dichotomy` | rr0-tarski-ideals | PASS | 4 §4.8 |
| `smoothing-normal-subgroup-cantor-dichotomy` | rr0-tarski-ideals | PASS | 4 §4.9 |
| `af-crossed-product-counterexample-normal-form` | rr0-tarski-ideals | PASS, Rainone 4.17 verbatim | 4 §4.10 |
| `moutzouris-singular-subgroup-has-vanishing-trace` | bk-glued-uct | PASS, quotes verbatim | 5 §5.1 |
| `moutzouris-k0-killing-is-local` | bk-glued-uct | PASS | 5 §5.1 |
| `brown-dadarlat-ext-trivial-class-gives-qd-extension` | blackadar-kirchberg | PASS, quotes verbatim | 5 §5.1 |
| `gabe-no-compact-open-prim-embeds-in-cone` | blackadar-kirchberg | PASS, quotes verbatim | 5 §5.1 |
| `bk-uct-counterexample-radical-not-projection-generated` | bk-glued-uct | PASS | 5 §5.2 |
| `bk-radical-traces-vanishing-on-boundary-are-zero` | bk-glued-uct | PASS | 5 §5.3 |
| `bk-radical-projection-quotients-are-toeplitz-infinite` | bk-glued-uct | PASS | 5 §5.4 |
| `bk-projection-generated-ideals-with-uct-quotients-force-qd` | bk-glued-uct | PASS | 5 §5.5 |
| `o2-free-range-projection-homotopy-iff-halving` | k1-halving-homotopy | PASS | 5 §5.6 |
| `o2-ideal-finite-nucdim-counterexample-unital-quotients` | k1-halving-homotopy | PASS, Robert verbatim | 5 §5.7 |
| `o2-ideal-projection-unit-witness-fails-cancellation` | k1-halving-homotopy | PASS | 5 §5.8 |
| `self-similar-hilbert-cx-module-has-unit-section` | k1-halving-homotopy | PASS | 5 §5.9 |
| `block-balanced-towers-have-central-halving` | tw-projection-starved-bundle | PASS | 6 §6.1 |
| `closed-extreme-trace-sets-give-r-fibre-w-star-bundles` | tw-projection-starved-bundle | PASS | 6 §6.2 |
| `central-halving-trivializes-every-closed-bauer-face-bundle` | tw-projection-starved-bundle | PASS, Ozawa import unreviewed | 6 §6.3 |
| `hopf-doubling-tower-has-no-m2-but-divides-unit-tracially` | tw-projection-starved-bundle | PASS | 6 §6.4 |
| `tensor-tower-bundle-trivial-iff-tails-softly-split` | tw-projection-starved-bundle | PASS | 6 §6.5 |
| `toms-no-gamma-algebra-is-trivial-on-closed-bauer-faces` | tw-projection-starved-bundle | PASS, Toms import unreviewed | 6 §6.6 |
| `pmf-permanence-amenable-kernel-without-exactness` | sl3z-purely-matricial | PASS | 6 §6.7 |
| `affine-sl2z-purely-matricial-field` | sl3z-purely-matricial | PASS | 6 §6.8 |
| `sl3z-pmf-iff-affine-kazhdan-group-pmf` | sl3z-purely-matricial | PASS | 6 §6.9 |
| `mdls-obstruction-is-affine-mechanism-plus-level-matching` | sl3z-purely-matricial | PASS, MdlS not re-read | 6 §6.10 |
| `sl3z-prime-level-invariant-witnesses-are-complete` | sl3z-purely-matricial | PASS | 6 §6.11 |
| `sl3z-prime-level-sc-forces-congruence-sc-for-sl2z` | sl3z-purely-matricial | PASS | 6 §6.12 |
| `sl3z-prime-level-sc-needs-cubic-chebotarev-primes` | sl3z-purely-matricial | PASS | 6 §6.13 |
| `congruence-sc-fails-along-levels-with-recurring-divisor` | cubic-division-strong-convergence | PASS | 6 §6.14 |
| `cubic-division-congruence-sc-descends-to-thin-subgroups` | cubic-division-strong-convergence | PASS | 6 §6.15 |
| `cubic-division-congruence-sc-forces-asymptotic-laplace-gap` | cubic-division-strong-convergence | PASS | 6 §6.16 |
| `bernoulli-shift-weak-k-equivalence-and-going-down` | bc-measured-coefficient | PASS, CEKN and BD verbatim | 7 §7.1 |
| `bernoulli-bc-splits-into-host-and-cylinder-comparison` | bc-measured-coefficient | PASS | 7 §7.2 |
| `bernoulli-assembly-injective-beyond-the-host` | bc-measured-coefficient | PASS, every host re-derived | 7 §7.3 |
| `module-defect-needs-non-k-exact-host` | bc-module-monster | PASS | 7 §7.4 |
| `monster-bc-detector-lives-on-a-proper-orbit-ideal` | bc-module-monster | PASS as import, Finn-Sell verbatim | 7 §7.5 |
| `osajda-monster-hosts-for-bc-module-route` | bc-module-monster | PASS as import, not re-read | 7 §7.6 |
| `bdl-deligne-type-two-norm-inapproximability` | nh-deligne-hs | PASS, verbatim | 7 §7.7 |
| `blsw-real-lattice-frobenius-stability` | nh-deligne-hs | PASS, verbatim | 7 §7.7 |
| `deligne-covers-of-sp2g-z-have-finite-residual-2z` | nh-deligne-hs | PASS, verbatim | 7 §7.7 |
| `kt-wreath-models-never-round-on-the-vertex` | hs-instability-extension | PASS, five premises unreviewed | 7 §7.8 |
| `cuntz-sups-with-continuous-rank-converge-uniformly` | rank-toms-b-construct | PASS | 7 §7.9 |

## 3. Part files

- `ex-review2-analysis-2026-09-13-part1.md`: the class-four chain (λ-mod-8 trapping over quaternionic
  Grassmannians), the transfer theorem, the gluing proposition, and the depth limits of rank-two and
  rank-N trapping.
- `ex-review2-analysis-2026-09-13-part2.md`: strict comparison divides the unit over C-space Bauer boundaries
  (staircases, orthogonalizing moves, summable and metric criteria), and the Toms-algebra diagonal quotient and
  twisted-halves rigidity, checked against arXiv:2606.12188v2.
- `ex-review2-analysis-2026-09-13-part3.md`: detection for Z/p-actions (Meyer--Nadareishvili sufficiency, the
  cellular-plus-phantom splitting, the (D)/(L)/(S)/(K) equivalences), and the O_2 dynamics (Rokhlin iff
  contractible, fixed central sequences, half-flip and McDuff), with Gabe--Szabó quotes checked verbatim.
- `ex-review2-analysis-2026-09-13-part4.md`: the RR0 dichotomy lanes (coinvariant Tarski lemma, order divisibility
  of AF K_0, crossed-product dichotomies for AF, integer, RR0-sr1 and Cantor coefficients, the counterexample normal
  form), with Rainone 4.17, OPR 5.16, 5.17, 4.3 and Ara--Goodearl 2.3 checked verbatim.
- `ex-review2-analysis-2026-09-13-part5.md`: the Blackadar--Kirchberg radical trace steps (Theorems 1, 5, 7, 8, 9 and
  corollaries), and the K1 halving lanes (projection form of the halving homotopy, O_2-multiplier ideals of finite
  nuclear dimension, cancellation, unit sections), with Moutzouris, Brown--Dadarlat, Gabe, BRR and Robert checked.
- `ex-review2-analysis-2026-09-13-part6.md`: W*-bundles over closed faces (central halving, the Hopf doubling tower,
  soft tail splittings, Toms's algebra on faces), SL_3(Z) matricial fields (amenable-kernel permanence, the affine
  reformulation, prime-level witnesses and forced Ramanujan consequences), and congruence strong convergence for
  cubic division lattices.
- `ex-review2-analysis-2026-09-13-part7.md`: Baum--Connes at Bernoulli coefficients (weak K-equivalence, host splitting,
  injectivity over every host), the module-route host constraints, the Deligne and stability imports, the wreath
  rounding no-go, and uniform convergence of Cuntz suprema.
- `ex-review2-analysis-2026-09-13-part8.md`: the K1-kernel of unital AH component groups is locally finite. This was the
  one census claim missed by parts 1--7, and a reconciliation of census ids against verdict rows caught it.
- `ex-review2-analysis-2026-09-13-part9.md` (wave-2 priority review, outside the census): the Pauli tower's nontrivial
  R-fibre W*-bundle (BBSTWW Question 3.14), with PASS on Theorems A, B and C and on fidelity to Definition 3.1; and
  negative answers to CCEGSTW Questions 1.5 (routes via Toms and via the Pauli tower) and 5.29 (via Toms), with PASS and
  every definition read verbatim.
- `ex-review2-analysis-2026-09-13-part10.md` (wave-2 priority review): Rainone's page-33 question, answered in
  substance by Boldrini--Prasad arXiv:2607.01896. PASS on the minimal Cantor realization, the generic-witness Baire
  argument, fidelity to Rainone's Theorem 4.22 hypotheses, and the failure of almost unperforation. Credit to
  Boldrini--Prasad is present on every node; BP 6.10, 6.12 and Wehrung 4.7.10, 4.7.14 were checked verbatim.
- `ex-review2-analysis-2026-09-13-part11.md`: census of the fourteen wave-2 operator lanes at tip `59ea57d883`. Of 39
  established claims without a PASS, 33 remain after parts 9 and 10.
- `ex-review2-analysis-2026-09-13-part12.md` (priority): the KK norm functor. PASS at p = 2 on Theorem A, Theorem B and
  the Rokhlin property of the flip on O_2 ⊗ O_2. GAP at odd p: in Proposition 1 the cross terms of F̃² need the
  partition operators to commute modulo compacts, and nothing supplies that.
- `ex-review2-analysis-2026-09-13-part13.md` (priority): Toms's rank theorems on block-diagonal realizers in the
  non-simple limit A and the simple algebra B. PASS, with wording notes: the hypothesis must hold at every large stage,
  one justification is wrong, and requires are missing. Section 4, Lemma 2 and Proposition 4 were checked against
  arXiv:2606.12188v2.

## 4. Outcome of the census

- **Verdicts.** All 86 census claims were reviewed: 86 PASS, 0 FAIL, 0 GAP. Parts 1--7 covered 85. The reconciliation
  added the 86th (part 8), and the id check found no other gap.
- **Graph fix.** One, landed at `d16d59955a`: requires for `zp-detection-iff-bootstrap-sufficiency-and-kk-g-generation-proof`.
- **Wording notes.** Three, each sent to its owner: the cut levels and inactive members in tw-rotation-gluing, and the
  left-sided compression in rank-toms-b-obstruct.
- **No false establishment.**
  - The only root that flips is the repository-built class-four root, and its chain passes.
  - The Rank Problem, Toms--Winter, UCT, LXI, RR0, Blackadar--Kirchberg, MF-Kazhdan, SL_3(Z) PMF,
    non-hyperlinear-group and Baum--Connes roots stay open.
- **Unreviewed established prerequisites** met during the review and not re-derived here, recommended for the next
  verifier:
  - `r-fibre-bundle-triviality-iff-uniform-central-halving` and `toms-ah-counterexample-to-uniform-gamma`;
  - `amenable-kernel-bc-transfer-and-ktop-half-exactness` and `lueck-surjective-assembly-traces-lie-in-lambda-g`;
  - the five vertex-rounding premises of §7.8 in part 7;
  - `izumi-rokhlin-approximately-representable-duality`.
