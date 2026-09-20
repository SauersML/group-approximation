# Hyperbolic residual finiteness: coordinated campaign, 20 September 2026

The requested target is still OPEN. No counterexample, universal residual
finiteness theorem, or proof of GHB7 flexible HS stability was obtained.
This campaign used all four available concurrent agent slots: three research
lanes plus the coordinating lane. Results below have written proofs and
independent mathematical reviews; they are not new Lean certifications.
No claim of literature novelty is made.

## Results wired into Cairn

1. **Quadratic padding, linear error.**
   `hrf-cyclic-edge-quadratic-padding` improves the preparation of cyclic-edge
   triangle matching from O(epsilon d) padding and O(sqrt(epsilon)) errors
   to O(epsilon² d) padding and O(epsilon) errors. The existing qualitative
   one-edge reduction now consumes this lemma. Spectral multiplicities are
   correctly treated as integer ranks. This does not remove the last edge
   mismatch.

2. **Localization to one expanding block.**
   `hrf-ghb7-expanding-block-localization` uses the accepted Liu fixed-tolerance
   block theorem to reduce flexible stability of finitely presented Kazhdan
   groups to uniform rounding on single scalar-expanding tuples. It retains
   doubled generators and fixes the discarded tolerance before selecting
   the expansion gap. Its GHB7 specialization is an equivalent OPEN target,
   `hrf-ghb7-scalar-expander-rounding`.

3. **A proved GHB7 rounding subclass.**
   `hrf-ghb7-scalar-relator-models-round-strictly` identifies integral H2 as
   the sum of the three vertex multipliers, hence killed by 2401. If all
   eleven relators evaluate to exact scalars and their maximum error is
   delta < 2 sin(pi/2401), all eight commutator relators are already exact.
   Scalar corrections to the three generators then give a genuine
   representation in the original dimension with operator-norm error at
   most (pi/14)delta. No expansion hypothesis is needed. This specializes
   the existing finite-multiplier principle quantitatively; it does not
   solve arbitrary matrix-valued defects. The strengthened
   `hrf-ghb7-central-relator-models-round-strictly` also handles relator
   matrices commuting exactly with all generators. Joint eigensectors
   reduce the generators; the mass of sectors with a nontrivial commutator
   phase is bounded by their squared defects. Correcting the other sectors
   and putting trivial representations on those bad sectors gives a
   dimension-independent linear normalized-HS bound, still with no padding.
   This extension passed independent review.

4. **A direct route to non-residual-finiteness.**
   `hrf-audit-stability-forces-prime-central-finite-residuals` proves that
   flexible stability of the base of a Kazhdan integral central extension
   bounds all finite central orders. Almost every prime central reduction
   therefore has its entire central kernel in the finite residual. The
   route `hrf-nonrf-via-stable-kazhdan-central-prime` feeds this into the
   requested root. The OPEN stable hyperbolic Kazhdan positive-b2 premise
   is indispensable; the argument does not construct it.

5. **Exact finite-detector tests and a larger exclusion.**
   `hrf-alt-edge-twist-finite-detector-spectrum` identifies finite central
   detectors of perfect-vertex twists through Schur-multiplier lift
   discrepancies. `hrf-alt-persistence-needs-sylow-detours` records why
   one kernel's pro-p tower cannot test all finite covers. For p>=5,
   `hrf-alt-psl2-detectors-need-new-composition-factors` excludes every
   detector quotient whose composition factors are PSL2 groups or cyclic
   groups of order different from p. Cyclic p-factors and other simple
   factors remain unexcluded, so this is not persistence.

## Checks that prevent invalid conclusions

The audit rechecked finite-index stability descent and the downstream
central-extension chain. The stronger nonhyperlinearity theorem uses
Dogon--Vigdorovich v2 (23 June 2026), not the weaker v1 formulation.

`hrf-audit-projective-internality-does-not-round` supplies nonroundable
projective models with exact internal commutants and fixed scalar expansion
for other Kazhdan groups. Internality and expansion alone cannot prove
GHB7 stability. The GHB7 finite multiplier and invariant-sector argument
remove the exact-central obstruction; induction from its positive-b2
subgroup can produce defects outside that subclass.

The existing HA description now distinguishes a restricted search by
commutant conjugations from the full allowed changes of vertex data.
The arithmetic discussion no longer claims universal failure of rank-one
CSP; its quaternionic candidates remain open. The alternative lane also
found that several recorded first-level full-moment calculations follow
from vanishing already present in their hypotheses, so they are not
independent evidence for persistence in all covers.

## Proof artifacts and review

- `hyperbolic-rf-quadratic-edge-preprocessing-2026-09-20.md`: coordinating
  lane proof; independently reviewed by the alternative-route lane.
- `hyperbolic-rf-ghb7-2026-09-20.md`: matching lane; localization reviewed
  by the audit lane, and the quantitative scalar-relator result reviewed
  independently by both the audit and coordinating lanes. The exact-central
  extension was also independently reviewed by the audit lane.
- `hyperbolic-rf-stability-audit-2026-09-20.md`: audit lane; the direct
  finite-residual theorem and metric normalization independently reviewed
  by the alternative-route lane.
- `hyperbolic-rf-alternatives-2026-09-20.md`: alternative lane; all detector
  and composition-factor results independently reviewed by the audit lane.
  The coordinating lane supplied and checked the all-PSL2 extension.

Graph compilation verifies schema and dependency bookkeeping, not the
mathematical proofs. The final `compile_graph` load, lint, and dependency
computation returned **zero errors and 47 warnings** across the repository
(10 restatement and 37 cycle warnings). No finding names a new `hrf-*`
node, and no new noncycle finding appeared relative to the baseline.
Two cycle warnings touching the residual-finiteness root match the
baseline exactly. All new theorem nodes derive ESTABLISHED, while the
scalar-expander frontier, HA, GHB7 stability, and the requested root
remain OPEN. Full `cairn check --json` runs ended with exit 143 before
returning output, so full duplicate/policy checking was not completed.
The machine-readable receipt is
`research/artifacts/hrf-ghb7-targeted-validation-2026-09-20.json`.
Unrelated concurrent work was not reverted or overwritten.

## Remaining decisive work

Prove dimension-uniform rounding for the GHB7 doubled-presentation scalar
expanders with general relator defects, or exhibit an instability sequence.
The exact-central correction gives no way to make arbitrary defects
commute exactly with the generators. On the finite-detector route, control
the remaining composition factors and lift discrepancies, or construct one actual
detector and eliminate that persistence candidate. Neither remaining
requirement has been established.
