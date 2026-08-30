---
rg: 2
id: quarter-native-chart-pays-fixed-hecke-displacement
kind: claim
title: A moving quarter-profile native chart pays fixed Hecke-frame displacement
artifacts:
  - research/moving-quarter-fixed-frame-distance-proof.md
distinct_from:
  near-full-hecke-source-cannot-retain-quarter-native-profile: that proves a quarter-profile subprojection of the fixed balanced Hecke chart must discard one third of the source; this permits an arbitrary moving source chart and proves that its pulled-back native sign must instead remain a fixed Hilbert--Schmidt distance from the fixed Hecke sign.
  moving-signed-source-does-not-localize-paid-sheet-detector: that proves the presently named sheet detectors have no useful compression on a moving signed-source cut; this gives a word-independent quantitative condition which every future moving quarter chart must satisfy.
  center-chain-common-source-authenticates-native-covariances: that asks full source-and-target-Gram typing of both native rows with vanishing loss; this isolates a necessary fixed-size source-frame displacement for its second row without refuting the possibility of an ordinary word which supplies that displacement.
---

**ESTABLISHED MOVING-CHART DISPLACEMENT FENCE.**  Retain the full signed
Hecke source and balanced second native sign

```text
Q=e_(L_0,lambda_0),        A=Q(1-t)/2,        tau(A)=q/2,
q=tau(Q)>0.                                                   (QMD1)
```

Let `E<=Q` have trace `beta=q-eta`, and let `B<=E` be the negative source
projection pulled back from a proposed moving native chart.  Suppose its
compressed negative fraction is within `zeta<1/4` of the required
second-row value:

```text
|tau(EBE)/beta-1/4|<=zeta.                                (QMD2)
```

Then

```text
||(A-B)E||_2^2
 >= max(0,(1/4-zeta)q-(3/4-zeta)eta).                    (QMD3)
```

In particular, if `eta,zeta=o(1)`, then

```text
||(A-B)E||_2 >= sqrt(q)/2-o(1).                          (QMD4)
```

For the corresponding source reflections `a=Q-2A` and `b=Q-2B`, this is

```text
||(a-b)E||_2 >= sqrt(q)-o(1).                           (QMD5)
```

Thus the second native quarter profile cannot be reached by a moving chart
whose pulled-back source sign is asymptotically the fixed balanced Hecke
sign, even if the retained cut is allowed to depend arbitrarily on the
matrix coordinate.  A successful source-and-target-Gram transition for
`center-chain-common-source-authenticates-native-covariances` must carry a
macroscopic source-frame displacement.  The displacement is not itself a
relator defect: an ordinary EL20 word may move the source by this amount.
What remains is to authenticate such a word's source and unequal target
Grams while cancelling its reservoir coboundary.

The limiting constant in `(QMD4)` is sharp at this abstract interface:
after finite amplification, choose `B<=A` with `tau(B)=q/4` and take
`E=Q`.  Then `||(A-B)E||_2^2=q/4`.

For the canonical center-chain source, `q=1/8192`; hence the limiting lower
bounds in `(QMD4)--(QMD5)` are respectively

```text
1/(128 sqrt(2)),                 1/(64 sqrt(2)).        (QMD6)
```

No Property `(T)`, canonical-trace substitution beyond the already exact
finite signed-source rank, computation, or literature theorem is used.

DERIVATION
moving-quarter-fixed-frame-distance-proof
