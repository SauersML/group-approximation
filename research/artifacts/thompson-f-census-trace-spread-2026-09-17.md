# Trace spread caps the Thompson-F census ratio; the census witnesses have frozen spread

Worker swarm-0917-w20-w20-nh-pull, 2026-09-17 wave. Experiments:
`experiments/thompson-f-witness-trace-test-2026-09-17/`.

## 0. Setup

- Presentation: `F = <a, b | R1, R2>`, with `R1 = [ab^-1, a^-1ba]` and `R2 = [ab^-1, a^-2ba^2]`.
- Commutator: `c = [a, b] = aba^-1b^-1`.
- Defect: for a unitary `X` in `(M_n, tr_n)`, `e(X) = ||X - I||_2^2 = 2 - 2 Re tr_n X`, so `0 <= e(X) <= 4`.
- Census ratio: for a pair `(U, W)`, `ratio(U, W) = e(c(U,W)) / max_i e(R_i(U,W))`.
- Constant: `C_n(F)^2` is the supremum of the ratio over `U(n)^2`.
- Known equivalence (`thompson-f-commutator-bound-holds-in-each-fixed-dimension`, item 3, and
  `thompson-f-hyperlinear-iff-relator-system-hs-unstable`): `F` is hyperlinear iff `sup_n C_n(F) = infinity`.
- Fixed-threshold census: `D_n(tau) = inf max_i e(R_i)` subject to `e(c) >= tau`.

**Fact (character simplex, `thompson-f-character-simplex`).** Every character of `F` has the form
`phi = t tau_reg + (1 - t) chi_ab`. It follows that `phi(w) = 1 - t`, a single number in `[0, 1]`, for every
`w` in `F' \ {e}`.

## 1. The spread lemma (proof)

Let `S = {w_1, ..., w_m}` be a finite subset of `F' \ {e}`. For a pair `(U, W)`, put `v(U,W) = (tr w_j(U,W))_j`,
a vector in `C^m`. Let `Delta_S` be the segment of constant real vectors `{(s, ..., s) : s in [0,1]}`.

- The **spread** is `sigma_S(U,W) = dist_inf(v(U,W), Delta_S)`, the sup-norm distance.
- `sigma_S >= eta` holds, for example, if two traces in `S` differ by `2 eta`, or if some `Re tr w_j <= -eta`.

**Lemma.** For every finite `S` in `F' \ {e}` and every `eta > 0`, there is `delta = delta(S, eta) > 0` with the
following property. Every pair of unitary matrices of any size `n` with `sigma_S(U,W) >= eta` satisfies
`max_i e(R_i(U,W)) >= delta`. Consequently `ratio(U,W) <= 4 / delta(S, eta)`, uniformly in `n`.

*Proof.*
1. Suppose not. Then there are sizes `n_k` and unitary pairs `(U_k, W_k)` in `U(n_k)` with `sigma_S >= eta` and
   `max_i e(R_i) <= 1/k`.
2. Fix a nonprincipal ultrafilter `omega` and form the tracial ultraproduct `(M, tau) = prod^omega (M_{n_k}, tr_{n_k})`.
   It is a tracial von Neumann algebra. The case of bounded `n_k` is included.
3. The classes `u = [U_k]` and `v = [W_k]` are unitaries in `M`, and
   `||R_i(u,v) - 1||_2 = lim_omega ||R_i(U_k,W_k) - I||_2 = 0`. So `R_i(u,v) = 1`, and `a -> u, b -> v` defines a
   homomorphism `pi : F -> U(M)`.
4. `phi = tau o pi` is a normalized positive-definite class function, that is, a character of `F`. For each `j`,
   `phi(w_j) = lim_omega tr w_j(U_k, W_k)`.
5. `sigma_S` is continuous in the trace vector, so the limit vector `(phi(w_j))_j` is at sup-distance at least `eta`
   from `Delta_S`.
6. The character simplex puts that vector in `Delta_S`, a contradiction.
7. Finally, `e(c) <= 4` gives the ratio bound. QED

The same proof works for pairs in any tracial von Neumann algebra: take the ultraproduct of the algebras.
The constant `delta(S, eta)` is not effective.

**Corollary 1 (the census above tau = 2 is bounded).** Take `S = {c}`. The condition `e(c) >= tau > 2` means
`Re tr c <= 1 - tau/2 < 0`, so `sigma_{c} >= tau/2 - 1`. Therefore `inf_n D_n(tau) >= delta({c}, tau/2 - 1) > 0`
for every `tau > 2`, whether or not `F` is hyperlinear. The fixed-`tau` census detects hyperlinearity only
for `tau <= 2`.

**Corollary 2 (what a divergent census must look like).** Suppose `F` is hyperlinear, and let `(U_k, W_k)` be any
sequence with `ratio -> infinity`. Then `sigma_S(U_k, W_k) -> 0` for every finite `S` in `F' \ {e}`.
- All nontrivial `F'` words must acquire equal real non-negative traces.
- A family whose spread on one fixed `S` stays above `eta` has ratio at most `4/delta(S, eta)`, in every dimension.

**Dilution (exact).** Let `(U, W) = (U_0, W_0) (+) (diag(alpha), diag(beta))`, where the second summand is
`(1-s)n` commuting scalars. Every `e`-value of a word in `F'` is then `s` times its value on the core. So the ratio
equals the core ratio. A witness at `tau <= 2` that is a dilution of a core with `e_core(c) > 2` inherits the core's
bound from Corollary 1.

## 2. The census witnesses (computation, float64)

Directory: `experiments/thompson-f-witness-trace-test-2026-09-17/`.

**Inputs.**
- `wit_F_n{16,32,64,64b,128}.npy` are the w19 fixed-`tau` census witnesses at `tau = 1.8`. They were extracted
  verbatim with `git show 3d20450385:experiments/thompson-f-defect-profile-2026-09-17/...`.
- Of these, `n16`, `n32`, `n64b` and `n128` are the configurations whose ratios w19 certified: 12.51, 15.91, 17.94
  and 20.16.

**Nontriviality.** `S_8` is the set of 17 cyclic-and-inversion classes of reduced `F'` words of length at most 8.
`check_classes.py` verifies in exact PL arithmetic over `Q` that every class is a nontrivial element of `F'`.
The PL maps are the standard generators, and the relators are checked to hold.
Output: `check_classes.out`, 17 classes and 0 failures.

**(a) Frozen spread.** `words6.py` produces `profiles_S8.out`. For each witness it reports `tr c` and the maximum over
`S_8` of `|tr w - tr c|`, called `Delta`. Here `c` is in `S_8`. If the trace vector lies within `sigma` of a
constant vector, then every entry is within `sigma` of that constant, so `Delta <= 2 sigma`. That is,
`sigma_{S_8} >= Delta/2`.

| witness | n | certified ratio | tr c | max over S_8 of \|tr w - tr c\| |
|---|---|---|---|---|
| wit_F_n16 | 16 | 12.51 | +0.100 | 0.453 |
| wit_F_n32 | 32 | 15.91 | +0.100 | 0.427 |
| wit_F_n64b | 64 | 17.94 | +0.036 | 0.396 |
| wit_F_n128 | 128 | 20.16 | +0.080 | 0.553 |

- Across these rungs the ratio grows 12.5 to 20.2, but the spread does not fall.
- `tr [a, b^2]` is about +0.53 to +0.61, whereas every character of `F` gives it the same value as `tr [a, b]`.
- An independent optimizer (`constrained_census.py`, `S = {c}`) reproduces the same profile:
  `wit_L4_n16` has spread 0.432 and `wit_L4_n32` has 0.388.

So `sigma_{S_8} >= 0.19` on every certified witness. By Section 1, the whole family has ratio at most
`4/delta(S_8, 0.19)`, a constant independent of `n`.

**(b) Diluted cores.** `blocks.py` splits a witness along the near-null space of `X -> (aX - Xa, bX - Xb)`.
It reports each block's leakage and, after polar correction, its `e`-values. Outputs: `blocks_n16.out`,
`blocks_n32.out` and `blocks_n64.out`.

| witness | core dim | leakage | core e(R1), e(R2) | core e(c) | core tr c | core ratio | rest |
|---|---|---|---|---|---|---|---|
| wit_F_n16 | 12 | 0.014 | 0.191, 0.189 | 2.400 | -0.200 | 12.60 | 4 dims, commuting, all e = 0 |
| wit_F_n32 | 23 | 0.003 | 0.158, 0.157 | 2.506 | -0.253 | 15.91 | 9 dims, commuting |
| wit_F_n64 (w19 warm, noise 0.03) | 45 | 0.002 | 0.161, 0.159 | 2.563 | -0.281 | 15.88 | 19 dims, commuting |
| wit_F_n64b (certified 17.94) | 50 | 0.006 | 0.137, 0.136 | 2.467 | -0.234 | 17.97 | 14 dims, commuting |

The `n64b` output is `blocks_n64b.out`.

- Each witness is, to within the leakage, a direct sum of one core and scalar pairs, which is the dilution of
  Section 1.
- Each core has `e(c) > 2`, so `Re tr c < 0`. No character of `F` takes a negative value on `c`.
- Within each core, the traces on `S_8` range over `[-0.25, +0.40]`. The regular character would make them all 0.
- By Corollary 1 and dilution, the census at `tau = 1.8` is being won by cores in the regime `tau > 2`. In that
  regime the census is bounded unconditionally.

**(c) What imposing `S_8` costs.** `impose.sh` produces `impose.out`. It restarts from the certified witnesses, at the
same `n`, with noise 0.01 and 1500 Adam steps, under two constraint sets:
- `L = 4`, the control: `e(c) >= 1.8`;
- `L = 8`: `e(w) >= 1.8` for all 17 classes, that is, `Re tr w <= 0.1`.

| start | L=4 ratio | L=8 ratio |
|---|---|---|
| wit_F_n16 | 15.75 | 6.78 |
| wit_F_n32 | 15.81 | 7.11 |
| wit_F_n64b | 17.25 | 7.22 |

The fresh multi-separation census has the following best values (`sweep.out`, `ladder_L8.out`):

| n | 4 | 8 | 16 | 32 | 64 |
|---|---|---|---|---|---|
| L=8 ratio | 3.4 | 5.7 | 7.2 | 7.3 | 6.8 |

The `L = 8` witnesses still have spread from 0.12 to 0.23 (`profiles_S8.out`). The reason is that `Re tr w <= 0.1`
bounds traces only from above, and the optimizer pushes a few classes negative.

**Honest scope.**
- (a) and (b) are float64 facts about the listed files.
- The optimizer is weak. Its warm ladders lose ground with `n`, so (c) is an upper bound on `D_n` and not a growth
  measurement.
- Nothing here separates `sup C_n < infinity` from `sup C_n = infinity`.
- What the computation does establish is that the existing ratio ladder (12.5 to 20.2) consists of configurations
  whose spread keeps them uniformly bounded. It is therefore not evidence of hyperlinearity.
- The informative census is the one constrained by `sigma_S <= eta`, with `eta` shrinking along the ladder.
  That census is open.
