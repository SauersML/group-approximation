---
rg: 2
id: fpbs-box-event-quadrant-k-arm-reduction
kind: claim
title: Two single-wedge K-arms of the wired boundary cluster (paths of I_n sites that may jump across pinch edges) force the FPBS pinch-wall box events D'_n(pi/2) and D'_n(0); hence (H) follows from one quadrant K-arm exponent alpha_Q < 3/16, or from alpha_Q < 23/96 given conditional decorrelation of the two arms on the one-arm event; triangular-lattice data give alpha_Q ~ 0.19 and decorrelation ratio kappa ~ 1.01, so the unconditional route sits on the threshold while the conditional route has margin 0.10 on the gate; on the one-arm event D'_n(0) equals the two-half-plane K-arm event exactly
distinct_from:
  fpbs-box-event-wedge-angle-law-refutes-restriction: that splits D'_n(pi/2) by FKG into two copies of the quadrant-target event D'_n(X^+), measured at rho ~ 0.211 > 3/16; this replaces the target-set events by increasing single-wedge arm events of the cluster itself, proves the two-arm inclusions by a Jordan crossing argument, and isolates the loss of FKG in one conditional-decorrelation inequality that the data put at kappa ~ 1
artifacts:
  - research/fpbs-box-event-quadrant-k-arm-reduction-proof.md
  - experiments/fpbs-wedge-k-arm-2026-09-18/karm.c
  - experiments/fpbs-wedge-k-arm-2026-09-18/exh.c
  - experiments/fpbs-wedge-k-arm-2026-09-18/pool.py
  - experiments/fpbs-wedge-k-arm-2026-09-18/pool_fast.py
  - experiments/fpbs-wedge-k-arm-2026-09-18/run_all.sh
  - experiments/fpbs-wedge-k-arm-2026-09-18/results.txt
---

**Status.** Theorem (a)-(d) below and Theorem 2.5 (the duality identity) are ESTABLISHED (proofs in
`fpbs-box-event-quadrant-k-arm-reduction-proof`, Sections 1-3). The
decorrelation inequality (CD) is OPEN; it is supported NUMERICALLY
(ratio `kappa_n` between 1.00 and 1.03 for `n = 8..512`, and `1.0033` by
exhaustive enumeration at `n = 3`). The exponent values are NUMERICAL.
(H) stays OPEN. Neither statement the previous step asked for, (i) the
widening inequality and (ii) `zeta(0) < 3/16`, is proved here; part (d)
proves that no FKG product of arm events can certify (ii).

**Setting.** Triangular site percolation at `p = 1/2`, wired box `B_n`,
boundary cluster `I_n`, negative axis `S_n`, pinch steps and the events
`D'_n(Y)` exactly as in
`fpbs-box-event-wedge-angle-law-refutes-restriction`. A *jump* joins
`a` to the far corner `b` of a lattice rhombus `a, u, b, v`; when `a`
and `b` lie in `I_n` the edge `uv` it crosses is a pinch. A *K-path* is
a path of `I_n` sites using adjacency and jumps. For a closed wedge `W`,
`A_n(W)` says the origin is in `I_n` and a K-path with all its sites in
`W` joins it to `∂B_n`. The wedges are the quadrants
`UL = {y >= 0, x <= 0}` and `LL = {y <= 0, x <= 0}` and the half-planes
`UH = {y >= 0}` and `LH = {y <= 0}`. Write `C_n = {0 ∈ I_n}`, with
`P(C_n) = n^{-5/48+o(1)}`, and `P(A_n(UL)) = n^{-alpha_Q+o(1)}`,
`P(A_n(UH)) = n^{-alpha_H+o(1)}`.

**Theorem.**

(a) *Two arms force the box events.*
`A_n(UL) ∩ A_n(LL) ⊆ D'_n(pi/2)` and
`A_n(UH) ∩ A_n(LH) ⊆ D'_n(0)`. A pinch-free non-`I_n` path cannot cross
a K-path (the jump segments cross only pinch edges), and a Jordan
crossing argument in the quarter or half of the box forces a crossing.

(b) *Product bounds.* Each `A_n(W)` is increasing, and the reflection
`y -> -y` maps `UL` to `LL`. By Harris-FKG,
`P(D'_n(pi/2)) >= P(A_n(UL))^2` and `P(D'_n(0)) >= P(A_n(UH))^2`.

(c) *Reduction of (H).* If `alpha_Q < 3/16`, then (H) holds. If also

    (CD)  P(A_n(UL) ∩ A_n(LL)) >= n^{-o(1)} P(A_n(UL)) P(A_n(LL)) / P(C_n),

then `alpha_Q < 23/96` already gives (H). In the same way (CD) for the
half-planes and `alpha_H < 7/48` would give (ii), `zeta(0) < 3/16`.

(d) *Obstruction to plain products.* Every `A_n(W)` lies in `C_n`. So
any bound `P(D'_n(0)) >= P(E) P(F)` with `E, F ⊆ C_n` gives at best
`zeta(0) <= 5/24`, which is above `3/16`. Statement (ii) cannot be
reached by FKG from arm events. It needs the sharing of the one arm,
which is exactly what (CD) records.

**Numerics** (`karm.c`, `n <= 512`; `results.txt`).

There were three Monte Carlo runs: 7189 samples at `n <= 256`, 1857 at
`n <= 512`, and 9861 in a quadrant-averaged run at `n <= 256`.
Exhaustive enumeration covered `n = 2` and `n = 3`.

| quantity | measured | threshold |
|---|---|---|
| `alpha_Q` (quadrant arm) | 0.190(3) | `< 3/16 = 0.1875` unconditionally, `< 23/96 = 0.240` with (CD) |
| `alpha_H` (half-plane arm) | 0.125-0.129 | `< 7/48 = 0.146` with (CD_H) gives (ii) |
| two quadrant arms | 0.262-0.272 | `2 alpha_Q - 5/48 = 0.276` |
| two half-plane arms | 0.144-0.155 | `2 alpha_H - 5/48 = 0.150` |
| `zeta(pi/2)`, `D'_n(pi/2)` | 0.265(7) | `3/8` |
| `zeta(0)`, `D'_n(0)` | 0.145(4) | `3/16` |
| one-arm | 0.101-0.105 | `5/48 = 0.104` |
| `kappa_Q`, `n = 8..512` | 1.00-1.03 | bounded below |
| `kappa_H`, `n = 8..512` | 0.992-0.999 | bounded below |

No sample violated the inclusions. The identity
`D'_n(0) ∩ C_n = A_n(UH) ∩ A_n(LH)` held in every one of about 60000
`(sample, n)` pairs. The two-arm events carry a fixed share of the box
events at every scale: about 0.68 of `D'_n(pi/2)` and about 0.64 of
`D'_n(0)`.

**Further proved result (Theorem 2.5, ESTABLISHED).**
`D'_n(0) ∩ C_n = A_n(UH) ∩ A_n(LH)`. To see this, flip the short
diagonal of every checkerboard rhombus. The result is a triangulation
whose black paths are the K-paths and whose white paths are the
pinch-free non-`I_n` paths. The Hex lemma in the upper and lower halves
then gives the identity. So on the one-arm event, statement (ii) is
exactly a statement about two half-plane K-arms.

**Mechanism.** Given `C_n`, the arm events fail only through *arcs*:
holes of `I_n` (pinch-free non-`I_n` components) that pass over the
origin inside the wedge, from one bounding ray to the other. The data
fit a picture in which such arcs occur at independent logarithmic scales
and at a constant rate, separately above and below the axis. Then
`alpha = 5/48 + lambda_W`, where `lambda_W` is the arc rate, and the
two-arm exponent is `5/48 + lambda_UL + lambda_LL`. That is (CD) with
`kappa` bounded.

**Next.** Prove (CD). Show that under the one-arm conditioning, which
converges locally to Kesten's incipient infinite cluster, the upper and
lower arc processes decouple across scales up to constant factors. That
is an arm-separation and quasi-multiplicativity statement for the
conditioned measure. With the measured `alpha_Q`, it closes (H) with
margin `0.10`.
