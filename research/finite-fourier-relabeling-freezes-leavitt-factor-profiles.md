---
rg: 2
id: finite-fourier-relabeling-freezes-leavitt-factor-profiles
kind: route
title: Round three involutions and relabel finite Fourier multiplicities after single-cycle trace tests
target: leavitt-finite-trace-tests-regularize-both-factor-profiles
requires:
  - leavitt-single-cycle-trace-controls-finite-sets
  - binary-leavitt-units-generated-by-c3-and-c2-cubed
artifacts:
  - research/artifacts/leavitt-finite-factor-profile-correction-2026-09-08.md
---

The seven nonidentity words of the second factor remain
nonidentity in the Leavitt group by the generation prerequisite.
The finite trace certificate bounds their evaluated traces by
`eta_0`, even before imposing exact second-factor laws.

Round each `B_i` to its nearest spectral sign, then average and
take signs successively to obtain commuting involutions `S_i`.
The normalized-HS sign-pinch estimate costs at most `sqrt(2)`
times the distance to the averaging algebra. The complete
three-generator calculation gives `||S_i-B_i||_2<=10 beta`.
Each of the seven product traces therefore has modulus at most
`eta_0+30 beta`.

Finite Fourier inversion gives character proportions `p_chi`.
A seven-sign Walsh calculation gives the sharp surplus bound
`f_B<=9*(eta_0+30 beta)/8`: the eight Walsh values are odd and
congruent modulo four, and their first two moments leave only
two possible absolute-value sums, `14` and `18`. Relabeling
surplus eigenspaces changes each involution in squared normalized
HS norm by at most four times this fraction.

For the first factor, the three proportions satisfy
`p_j-1/3=(2/3)Re(omega^(-j) tr C)`. Their total surplus is their
maximum absolute deviation, at most `2|tr C|/3`. Relabeling
different cube roots costs exactly three times the relabeled
fraction in squared normalized HS norm.

Both relabelings take place in the original dimension when
`24|n`. Telescoping gives the stated bound on every word,
including inverse letters. The artifact proves the elementary
rounding and Fourier statements directly and records the exact
fixed-C, dimension, and full-kernel quantifiers.
