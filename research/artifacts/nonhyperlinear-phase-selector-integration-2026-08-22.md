# Phase-selector breakthrough integration — 2026-08-22

This artifact records the delta integrated from the supplied
“Non-Hyperlinear Group Program” note.  It intentionally points to canonical
Cairn claims instead of duplicating their proofs.

## New established claims

- `phase-covariance-words-exactly-measure-type-transport-leakage` proves the
  two-sided phase-code transport identity and its ordinary-word form.
- `phase-tagged-row-defect-reduces-to-within-type-selector-mismatch` proves
  the exact cross-type/within-type split for each cyclic selector row.
- `spectral-compressed-leakage-is-finite-word-moment-functional` Fourier-
  expands leakage whenever both cuts are already word-spectral.
- `monomial-game-pair-compatibility-is-projective-color-rigid` gives the
  general projective-color boundary behind the earlier Harris affine-support
  no-go.
- `finite-dimensional-kplus-does-not-factor-through-hinfinityplus` closes
  the weak-to-strong finite-dimensional quantum-reflection shortcut.
- `finite-unitary-canonical-trace-span-no-go`
  explains why finite packet groupification needs a protected projective
  phase sector.
- `cyclic-coarse-fine-selector-rows-spread-carrier-error` was strengthened in
  place from the `1/2` versus `1/4` special case to the exact coefficient
  `|a-b|` for arbitrary fixed selector ratios.

The note's Fourier normalizer/block-Gram theorem and phase-codeword Gram
corollary were already present as
`fourier-normalizer-words-control-block-gram-leakage` and
`finite-phase-codewords-weight-type-gram-leakage`; no duplicate nodes were
created.

## Endpoint after integration

The existing route `nonhyperlinear-via-phase-coded-gtc4` remains one claim
short.  Its open dependency `finite-phase-tags-authenticate-forbidden-cuts`
has been narrowed in place to the within-type estimate

```text
sum_omega
 ||Q_(sigma(omega))U_omega e_omega U_omega^*
   Q_(sigma(omega))-f_(sigma(omega))||_2^2
 <=C E_rel+o(1).
```

Cross-type population is now an exact phase-covariance calculation; off-type
Gram leakage is already an exact Fourier-normalizer calculation; `K_(2,m)`
already removes the multiplicity gauge.  The remaining analytic object is
the noncanonical forbidden-weighted cut `F_cQ_omega` inside the matched type.
For the common central-sign endpoint,
`marked-corner-cycle-needs-no-full-mass-concentration` means no separate
full-space marked-mass concentration hypothesis is load-bearing.

## Alternate monomial route

The one-step Harris-to-monomial shortcut is excluded by projective-color
rigidity, but `bisynchronous-to-monomial-game-algebra-compiler` deliberately
remains open for an auxiliary-incidence or trace-preserving full-corner
construction.  The finite-ancilla trace no-go explains why any successful
ordinary-group shadow is expected to retain a protected scalar phase.

## Supplied-paper routing without duplicate nodes

- arXiv:2608.14858 is already imported by
  `finite-phase-monomial-game-algebra-dictionary`; the new projective-color
  and weak-versus-strong claims delimit its usable compiler surface.
- arXiv:2608.16452 is already imported by
  `renyi-soft-covering-rate-floor-citation`.  The missing presentation-level
  rate cap is already audited, and in the direct dual-prefix model refuted,
  by `dual-prefix-renyi2-rate-gap` and its refuter.
- arXiv:2608.18405 is already imported by
  `relative-symmetry-norming-citation`.  Its adaptive detector does not give
  a fixed finite word menu, while
  `projectively-closed-symmetry-bases-are-hyperfinite` records the stronger
  multiplicative-closure firewall.
- The supplied channel, Fell-bundle ground-state, type-I normalized-power,
  and minimum-attainment papers do not presently supply canonical-trace
  promotion or a dimension-uniform normalized-HS inequality.  They are kept
  as source-audit observations here rather than promoted to unsupported
  proof dependencies.

## First post-integration attack on WITHIN

The explicit local predicate phase
`boolean-predicate-central-phase-word` was tested as a possible spectral
surrogate.  It does not close the gate: after a finite packet type is fixed,
packet words act identically on every anonymous multiplicity copy.  The live
forbidden cut is produced by the shared BCS tuple on that multiplicity space.
The existing theorem
`amplification-natural-words-cannot-read-packet-multiplicity` therefore rules
out a packet-only implementation of the surrogate.  Any viable WI word must
couple a packet phase to the shared source observables; simply adjoining the
finite predicate 2-group would duplicate the already-fenced controlled-phase
construction.
