---
rg: 2
id: clifford-long-codes-realize-pairing-value-in-binary-noise-test
kind: claim
title: Clifford long codes give entangled strategies for the binary noise test whose value is governed by SDP vectors, so fully rich 2-to-1 games of vanishing value have near-complete entangled test value
distinct_from:
  sd-rich-and-unique-games-sos-gaps-interconvert: that transfers SoS pseudo-distributions and classical values through the right merge and the noise test; this turns SDP 1 vectors into genuine entangled strategies of the test's output and proves a squared-SDP lower bound, which says nothing about SoS degree or classical value.
  derived-unique-game-lower-bounds-the-noise-test: that is a classical labeling lower bound on learnable matchings; this is an operator lower bound on fully rich inputs, where the classical soundness of the test is expected to hold.
  affine-long-code-test-has-no-uniform-soundness: that gives explicit classical folded labelings with high acceptance on low-value affine sources; this gives entangled, non-classical strategies on fully rich sources and refutes no classical soundness statement.
artifacts:
  - experiments/entangled-noise-test-2026-09-17/clifford_noise_test.py
  - research/artifacts/clifford-long-codes-pairing-vector-proof-2026-09-17.md
---

**OPEN.** A drafted proof is recorded as an attempt (see Attempts); it is not established because referees refuted the result as written. Let `Psi` be a 2-to-1
game with left alphabet `[2k]`, right alphabet `[k]` and constraints `pi_(u,b)`.
Let `R_(rho,2)(Psi)` be the folded long-code noise test with `m = 2`:

- pick `b` from the right marginal and `u, v` independently from the conditional
  neighbour law, which is the specified test on biregular instances;
- pick `A` uniform in `(Z_2)^k` and apply `K_rho` noise to get `B`;
- pull back `P_x = A_(pi_(u,b)(x))` and `Q_y = B_(pi_(v,b)(y))`;
- apply `K_rho` noise to get `X` and `Y`;
- accept iff `F_u(X) = F_v(Y)`.

It is played as a two-prover game with `(u,X)` sent to Alice and `(v,Y)` sent to
Bob.

**C1 (Clifford long codes).** Let `gamma_1, ..., gamma_D` be pairwise
anticommuting Hermitian unitaries of dimension `d = 2^ceil(D/2)`, and write
`gamma(w) = sum_i w_i gamma_i` and `tau = tr/d`. Then
`gamma(w)^2 = |w|^2 I` and `tau(gamma(w) gamma(w')) = <w, w'>`.

For each `u`, choose orthogonal `w_(u,x) in R^D` (`x in [2k]`) with
`sum_x |w_(u,x)|^2 = 1`. Then
`F_u(X) = gamma(sum_x (-1)^(X_x) w_(u,x))` is a `+-1` observable, and it is folded:
`F_u(X + 1) = -F_u(X)`. The influence of coordinate `x` is `|w_(u,x)|^2`.

**C2 (value identity).** Alice measures `F_u(X)` and Bob measures
`conj(F_v(Y))` on the maximally entangled state. The acceptance probability is

```text
1/2 + (rho^3/2) E_b sum_(j in [k]) | E_(u|b) W_(u,b,j) |^2,
W_(u,b,j) = sum_(x in pi_(u,b)^(-1)(j)) w_(u,x).
```

Write `PV(Psi)` for the supremum of the double sum over all frames. Then
`val*(R_(rho,2)(Psi)) >= 1/2 + (rho^3/2) PV(Psi)`.

**C3 (right merge).** Let `U` be a unique game with alphabet `[2k]` and let
`Psi(U)` be its right merge (`sd-rich-and-unique-games-sos-gaps-interconvert` (a)).
Then `PV(Psi(U)) >= omega_sdp1(U)^2`.

**C4 (consequence).** Along even `k`, take the Khot--Vishnoi unique games quoted in
`unique-games-entangled-value-approximable-by-sdp-citation`. They satisfy
`omega_sdp1 >= 1 - 9 eta` and `val <= 2/k^eta`. Their right merges are fully rich
2-to-1 games with

```text
val(Psi(U)) <= 4/k^eta -> 0,
val*(R_(rho,2)(Psi(U))) >= (1 + rho^3 (1 - 9 eta)^2)/2.
```

The honest classical completeness of the test, dictators on a satisfying
labeling, is `(1 + rho^3)/2`.

So, for every `delta < (1 + rho^3)/2` and `eta' > 0`, no binary inner decoder
satisfies `D_cl` of `entanglement-sound-soundness-cannot-prove-ugc`, not even
restricted to fully rich inputs and to maximally entangled Clifford strategies.
This kill is unconditional; it does not assume `P != NP`.

**Scope.** Braverman--Khot--Minzer take `m` large, so this refutes no published
theorem. For general `m` the kill of entanglement-robust soundness is the
conditional B1/B2 of the parent claim. A clock-and-shift (generalized Clifford)
analogue for `m > 2` is not claimed. The script checks C1 and C2 exactly, through
the trace formula and an explicit kron-product strategy, on a 2+2-vertex unique
game with alphabet 4 merged over all six pairings. It checks the inequality of C3
on random nonnegative frames. It proves nothing asymptotic.

## Attempts

- 2026-09-17 `swarm-0917` (ugc-pull-1): candidate direct proof, held OPEN. The route was withdrawn to `research/artifacts/clifford-long-codes-pairing-vector-proof-2026-09-17.md`.
  Referee lens 1 returned *refuted*: B3 parts 2 and 3 use "x in L => val(O(x)) >= 1 - eta" and that `O` runs in polynomial time, but the B3 statement never assumes either (only `R` gets a completeness hypothesis); as written B3.2 is equivalent to P != NP (if P = NP, send every input to a fixed value-0 game and let `R` decide Gap-2to1 and output a fixed game, while `L` is outside P by the time hierarchy). Referee lens 2 returned *refuted*: the "dead as a class" bullet added to `rich-2to1-games-conjecture` overclaims, since KRT Theorems 1.3 and 4.5 need a unique game and KRT's only 2-to-1 result (Theorem 4.8) needs SDP value exactly 1; so nothing here rules out an entanglement-sound outer PCP to rich 2-to-1 games followed by the classically sound noise test, contradicting the claim's own "only composition left open" sentence. Lens 3 returned *survives* with the same missing-hypothesis caveat plus a midpoint-threshold remark for B1. All three lenses found B1, B2, the commuting-operator extension, C1--C4 and the KRT quotes sound, and `clifford_noise_test.py` passes.
