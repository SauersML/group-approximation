---
rg: 2
id: fpbs-cd-h-exact-decomposition-and-renewal-obstruction
kind: claim
title: The FPBS axis-to-axis box event splits exactly as D'_n(0) = U_n ∩ L_n into two increasing reflected half-plane events with A_n(UH) = C_n ∩ U_n, and a one-site flip gives P(D'_n(0)) <= 2 P(D'_n(0) ∩ C_n); hence (ii) zeta(0) < 3/16 is equivalent to the two half-plane arms gaining a correlation factor of at least n^{2 alpha_H - 3/16 + eps} over FKG, and (CD_H) is equivalent to the exponent bound zeta(0) <= 2 alpha_H - 5/48; an independent-scales product model with all of these structural properties has no gain at all, so neither arm separation nor quasi-multiplicativity nor FKG can prove (CD_H) or (ii); the exact n = 3 value kappa_H = 0.999969 < 1 kills conditional positive association
distinct_from:
  fpbs-box-event-quadrant-k-arm-reduction: that proves D'_n(0) ∩ C_n = A_n(UH) ∩ A_n(LH) on the one-arm event only, and leaves (CD) open as an inequality between arm events that are all contained in C_n; this removes the one-arm conditioning altogether (D'_n(0) = U_n ∩ L_n on every configuration, with U_n and L_n not contained in C_n), bounds the one-arm loss by a factor of 2, turns (ii) into a pure correlation-gain statement for two increasing events, and proves that the conditional decorrelation it asked for is not a consequence of the structural tools it proposed
artifacts:
  - research/fpbs-cd-h-exact-decomposition-and-renewal-obstruction-proof.md
  - experiments/fpbs-cd-renewal-2026-09-19/dec.c
  - experiments/fpbs-cd-renewal-2026-09-19/run_all.sh
  - experiments/fpbs-cd-renewal-2026-09-19/results.txt
---

**Status.** Theorems A, B and C are ESTABLISHED (full proofs in
`fpbs-cd-h-exact-decomposition-and-renewal-obstruction-proof`, Sections
1-4), and checked by exhaustive enumeration at `n = 3` and by sampling up
to `n = 128`, with no violations. Theorem D (the structural obstruction)
is ESTABLISHED. The route to (CD_H) through arm separation,
quasi-multiplicativity and FKG under one-arm conditioning is DEAD: the
exact failing step is in Section 5 of the proof. (ii) and (H) stay OPEN.
The exponents are NUMERICAL.

**Setting.** As in `fpbs-box-event-quadrant-k-arm-reduction`. Triangular
site percolation at `p = 1/2` in the wired box `B_n`, with boundary cluster
`I_n`. `C_n = {0 ∈ I_n}` and `S_n = {(i,0) : -n < i <= 0}`. Let
`P_n = {(i,0) : 1 <= i <= n-1}`. Pinch steps, K-paths, `A_n(UH)` and
`A_n(LH)` are as there. A *white path* means a path of sites of `B_n` not
in `I_n` that uses no pinch step. Let

* `U_n` = no white path with all sites in `{j >= 0}` joins `S_n` to `P_n`;
* `L_n` = the same with `{j <= 0}`.

**Theorem A (exact decomposition).** For `n >= 2`, `U_n` and `L_n` are
increasing, and the reflection `(x,y) -> (x,-y)` exchanges them. On every
configuration,

    D'_n(0) = U_n ∩ L_n,   A_n(UH) = C_n ∩ U_n,   A_n(LH) = C_n ∩ L_n.

The identity of the previous step, `D'_n(0) ∩ C_n = A_n(UH) ∩ A_n(LH)`,
is the intersection of these.

**Theorem B (local forcing and the one-site flip).** On `U_n`, either
`0 ∈ I_n`, or `(1,0) ∈ I_n`, or both `(0,1)` and `(1,-1)` lie in `I_n`.
Consequently `P(E) <= 2 P(E ∩ C_n)` for every increasing `E ⊆ U_n`. In
particular `P(U_n) <= 2 P(A_n(UH))` and `P(D'_n(0)) <= 2 P(D'_n(0) ∩ C_n)`.

**Theorem C (what (ii) and (CD_H) are).** Put
`rho_n = P(U_n ∩ L_n) / (P(U_n) P(L_n))`, which is `>= 1` by FKG. Then
`rho_n P(C_n) / kappa_H(n)` lies in `[1/4, 2]`, where
`kappa_H(n) = P(A(UH) ∩ A(LH)) P(C_n) / (P(A(UH)) P(A(LH)))`. If `alpha_H`
exists:

* (ii) `zeta(0) < 3/16` holds iff `rho_n >= n^{2 alpha_H - 3/16 + eps}`
  for some `eps > 0` and all large `n`, iff (CD_H) holds with a loss
  `kappa_H >= n^{-delta}` for some `delta < 7/24 - 2 alpha_H`;
* (CD_H) holds iff `zeta(0) <= 2 alpha_H - 5/48`, iff
  `rho_n >= n^{5/48 - o(1)}`. This is an identity of exponents whenever
  also `kappa_H <= n^{o(1)}`, which the data show (`kappa_H < 1`).

**Theorem D (structural obstruction).** There is a family of product
measures on `{0,1}^{2K}` with increasing events `C ⊇ U' , L'` that have all
the structure used above. The structure is: reflection symmetry
exchanging the two arms; `U' ∩ C` and `L' ∩ C` are the arm events; the
flip bound; independence across `K` scales, so that quasi-multiplicativity
holds with constant 1; and FKG. In this family `rho = 1` exactly and
`kappa = (2p - p^2)^K = n^{-delta}` with `delta > 0`. So no argument that
uses only these properties proves (CD_H), or even the weak form (ii)
needs. The gain `rho_n` has to come from lattice-specific input.

**Numerics (NUMERICAL).** Every sampled configuration satisfies Theorems
A and B. The data give `rho_n P(C_n)` roughly equal to `kappa_H`, which is
`0.99997` at `n = 3` (exact) and falls to `0.9923(15)` at `n = 512`, so
`delta_H` is about `0.002`. The target margin is `7/24 - 2 alpha_H`, about
`0.037`. So (ii) is numerically true with room to spare, and the measured
`zeta(0) = 0.145(4)` fits the value `2 alpha_H - 5/48 = 0.150` predicted
by (CD_H). The data fit the values `alpha_H = 1/8` and
`zeta(0) = 7/48`, but these are CONJECTURES.

**Next step.** Prove `rho_n >= n^{0.067}` directly, that is
`P(D'_n(0)) >= n^{-3/16+eps}` for the single increasing event
`D'_n(0) = U_n ∩ L_n`. This must use a lattice-specific input: either the
SLE6 exploration of the white Γ_n-cluster of the slit, or an annulus-scale
sharing lemma with a quantitative constant. Section 6 of the proof has the
precise target.

## Attempts

- w20-123 (2026-09-19): target (CD_H) by arm separation and
  quasi-multiplicativity under one-arm conditioning. Result: exact
  decomposition, flip bound, and a proof that these tools cannot give
  (CD_H). The route is dead at the step "per-annulus decorrelation factor
  tends to 1" (proof Section 5).
