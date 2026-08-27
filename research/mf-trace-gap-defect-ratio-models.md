---
rg: 2
id: mf-trace-gap-defect-ratio-models
kind: claim
title: MF groups admit models whose squared defect beats their trace gap
distinct_from:
  mf-implies-hyperlinear: This is one explicit analytic profile sufficient for the root claim, not the root claim; it asks for a rate relating the multiplicative defect, the dimension, and the visibility of one element.
  countable-group-mf-conventions: That established claim compares MF formulations at fixed accuracy; this one asks for a quantitative dimension-versus-defect rate that no formulation supplies for free.
artifacts:
  - notes/FALSE_WEAK_MF_EFFECTIVE_RANK_PROFILE.md
  - notes/FALSE_ONE_NUMBER_RELATIVE_COMMUTANT_CRITERION.md
  - notes/NOTEPAD.md
  - GroupApproximation/Sofic/ExteriorMFProfile.lean
  - GroupApproximation/Sofic/NormTraceGap.lean
---

Let `G` be a countable MF group and `g != 1`.  Then there exist
operator-norm local models `phi_n : G -> U(d_n)` on exhausting
multiplication windows, with defects `epsilon_n` and trace gaps

```text
kappa_n = 1-Re tr_(d_n)(phi_n(g)),
```

such that

```text
epsilon_n^2/kappa_n -> 0.                                        (P1)
```

Two remarks fix the scale.  Operator separation with constant `1` forces
`kappa_n >= 1/(2 d_n)` for free, so `(P1)` is implied by
`epsilon_n sqrt(d_n) -> 0`; and if the deviation `phi_n(g)-1` has effective
rank `Omega(d_n)` then `kappa_n = Omega(1)` and `(P1)` is implied by
`epsilon_n -> 0`, which is automatic.  `(P1)` interpolates between these:
either the defect is small relative to the dimension, or the witness is
spread over positive density, or any trade-off between the two.

The gap is stated in terms of the *trace gap* `kappa_n` rather than the rank
of `phi_n(g)-1` deliberately: `NormTraceGap.phase_deviation_no_amplification`
shows a full-rank deviation (`i . 1`) can be amplification-invisible, so the
rank is the wrong invariant and the trace gap is the right one.

**This is the weaker of the cluster's two holes.**  By
`corner-visibility-gives-rate-profile` it is implied by
`mf-invariant-corner-visibility`, which demands `kappa_n` bounded below,
whereas `(P1)` tolerates `kappa_n -> 0` provided `epsilon_n^2` decays faster.
Attack this one.

**Where it fails, and where it is free.**  By
`sign-mark-rate-is-sector-density`, for a central involution mark the
statistic is `epsilon_n^2/(4 delta_n)` with `delta_n` the density of the
negative sector, so the profile is free whenever the mark occupies positive
density and is *refuted* whenever property `(T)` squeezes the mark onto a
sector of density `O(epsilon_n^2)` --- which is exactly what happens with
exact finite-dimensional ambient letters.  Any attempt on this claim should
therefore target models whose ambient sector is genuinely approximate; a
family with `(T)`-rigid exact ambients cannot satisfy it.

Nothing in the MF property relates `epsilon_n` to `d_n`; this claim is the
exact analytic content missing from `mf-implies-hyperlinear` along the
amplification route.  It is the repository's own stated subproblem: the
square-root-profile entry of `notes/NOTEPAD.md` (2026-08-08) closes with
"extracting or disproving this profile is now a concrete quantitative
subproblem", after observing that Shulman's qualitative MF theorem states no
such rate.  The special case `epsilon_n sqrt(d_n) -> 0` for a group already
known to be weak MF is that entry verbatim.
