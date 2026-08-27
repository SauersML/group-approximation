---
rg: 2
id: atlas-true-criterion-baseline-proof
kind: route
title: Closed-form traces at both classical warm starts, checked against the retraction count
target: atlas-true-criterion-baseline
requires: [atlas-steinberg-rank-five-translation, atlas-kernel-window-length-nine]
---

# Closed-form traces at both classical warm starts, checked against the retraction count

Unitarity turns the objective into traces:
`‖π(s) − I‖₂² = 2 − 2·Re tr π(s)`.  For an automorphism alignment,
`π(s) = λ(fold_θ(s))` and the normalized trace of a regular
representation is `1` at the identity and `0` elsewhere — whence the
`{0, √2}` dichotomy per relator, and max-defect `√2` for every
alignment since the fold screen (recorded on
`atlas-kernel-window-length-nine`) shows none kills the list.  For the
tensor flip, `π_J(s) = L_{p₁(s)} R_{p₂(s)}` and
`tr(L_a R_b) = #{g : g^{-1}ag = b}/|A₈|`, which vanishes unless
`a ∼ b`.  On each of the 72 escapees one projection is trivial and the
other a transvection — non-conjugate, trace exactly `0`, defect exactly
`√2`; on the 4,564 non-escapees both projections agree and the defect
is `0`.  The RMS identity `√(2·72/4636) = 0.176242` closes the
arithmetic loop, and the identification of the defect set with the
retraction-escaping set of `atlas-kernel-window-length-nine` is exact
set equality, not an estimate.  Executable reproduction in seconds:
`experiments/atlas_true_criterion_warmstarts.py`; full derivation,
measured cost model and staged campaign design:
`research/artifacts/atlas-true-criterion-probe-2026-08-15.md`.
