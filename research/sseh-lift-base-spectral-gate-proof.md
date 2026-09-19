---
rg: 2
id: sseh-lift-base-spectral-gate-proof
kind: route
title: Read the YES witness of the lift as a labeling by load rigidity, read the NO side as a value bound by the cylinder and labeling necessity, and feed both into the AKKSTV ratio gate on the base, then close with Cheeger against the base profile
target: sseh-lift-routes-need-spectrally-defective-bases
requires:
  - lift-yes-sets-are-labelings-unless-the-base-loses-a-cut
  - lifts-over-multiscale-expanders-expand-unless-ug-value-large
  - spectral-gap-ratio-reductions-cannot-prove-ugc
  - single-density-expansion-forces-the-multiscale-profile
artifacts:
  - experiments/sse-lift-base-gate-2026-09-18/check_load_rigidity.py
---

Notation is that of the target claim. `X(s)` is the threshold of
`spectral-gap-ratio-reductions-cannot-prove-ugc`: the least integer `x >= 3`
with `C_A log(x)/x < 1 - s`, where `C_A` is the absolute constant of the
imported AKKSTV rounding. `X` is non-decreasing in `s`, so for `eta <= 1/2` we
may write `X_0 = X(1/2) >= X(eta)`, an absolute constant, and
`theta = 5 X(eta) sqrt(eta) <= 5 X_0 sqrt(eta)`.

## (B0) The NO side

Let `x not in L`, so `Phi_L(1/q) >= 1 - eta` for `L = L(U(x))`. Item (3) of
`lifts-over-multiscale-expanders-expand-unless-ug-value-large` states
`1 - Phi_L(1/q) >= val(U)` (labeling sets) and
`1 - Phi_L(1/q) >= 1 - Phi_H(W)` for every `W` with `mu(W) = 1/q` (cylinders).
Hence `val(U(x)) <= eta` and `Phi_H(W) >= 1 - eta` for every such `W`, that is
`Phi_(H(x))(1/q) >= 1 - eta`. Nothing is assumed about `H(x)` here.

## (B1) The YES side

Let `x in L`, so some `S` of measure `1/q` in `L(U(x))` has `Phi_L(S) <= eta`.
The spectral trichotomy of
`lift-yes-sets-are-labelings-unless-the-base-loses-a-cut`, applied with
`eta_0 = eta`, gives one of

```text
(Y-lab)  val(U(x)) >= 1 - 5 sqrt(eta),
(Y-spec) lambda_2(H(x)) <= 4 sqrt(eta),
(Y-thin) mu(supp S) < sqrt(eta)/2.
```

## (B2) The gate

Assume the reduction is support-spread, so (Y-thin) never occurs. Put
`E = {x : lambda_2(H(x)) >= theta}`. Computing `lambda_2` of an explicitly given
graph is polynomial time, so `E in P`.

*Claim: `L n E in P`.* Define a second reduction `f'`:

- `f'(x) = U(x)` when `x in E`;
- `f'(x) = Z` when `x not in E`, where `Z` is the fixed two-vertex unique game
  over `Z_m` with `m = ceil(1/eta)` carrying all `m` shift constraints, so
  `opt(Z) = 1/m <= eta`.

Then `f'` is polynomial time, and:

- If `x in L n E` then (Y-thin) is excluded by hypothesis and (Y-spec) is
  excluded because `theta = 5 X(eta) sqrt(eta) >= 15 sqrt(eta) > 4 sqrt(eta)`
  (using `X >= 3`). So (Y-lab) holds, `1 - opt(f'(x)) <= 5 sqrt(eta)`, and
  `lambda_2(f'(x)) >= theta = X(eta) . 5 sqrt(eta) >= X(eta)(1 - opt(f'(x)))`.
  Also `lambda_2 >= theta > 0` and `H(x)` is loop-free regular by hypothesis.
- If `x not in L n E` then either `x not in E`, and `opt(f'(x)) = 1/m <= eta`,
  or `x in E` and `x not in L`, and `opt(f'(x)) = val(U(x)) <= eta` by (B0).

These are exactly the hypotheses of (K1) of
`spectral-gap-ratio-reductions-cannot-prove-ugc` with `s = eta` and source
`L n E`. That gate concludes `L n E in P`; its decider accepts iff
`val(AKKSTV(f'(x))) > eta`.

*Consequences.* If `lambda_2(H(x)) >= theta` for every `x in L`, then
`L <= E`, so `L = L n E in P`. In general, `E in P` and `L n E in P`, so if
`L \ E` were in `P` then `L in P`. Hence, unless `L in P`, `L` stays hard on the
**hard core** `E^c = {x : lambda_2(H(x)) < theta}`. That set therefore contains
both members and non-members of `L`: if it contained no member then `L <= E` and
`L in P`; if it contained no non-member then the decider "accept on `E^c`, run
the `L n E` decider on `E`" would decide `L`. So in the hard core the bases have
`lambda_2(H) < theta` on both sides. This is (B2).

## (B3) Forced shape of the base

Take `x in E^c` with `x not in L`. By (B0), `Phi_H(1/q) >= 1 - eta`; by (B2),
`lambda_2(H) < theta <= 5 X_0 sqrt(eta)`.

The Cheeger inequality for the normalized Laplacian (Alon--Milman; Chung,
*Spectral Graph Theory*, Theorem 2.3) gives, on a connected regular graph, a set
`B` with `mu(B) <= 1/2` and

```text
Phi_H(B) <= sqrt(2 lambda_2(H)) < sqrt(10 X_0) eta^(1/4) =: kappa.
```

`kappa <= 1/2` exactly when `10 X_0 sqrt(eta) <= 1/4`, that is
`eta <= (40 X_0)^(-2) =: eta_0`, an absolute threshold. Assume `eta <= eta_0`.
Then `kappa <= 1/2 < 1 - eta`, so `mu(B) != 1/q`.

**This is where the route stops being unconditional.** Everything above uses
only `Phi_H(1/q) >= 1 - eta`, which the necessity half does force on NO outputs;
what follows needs the multiscale profile (N2) across the whole window, which it
does **not** force. Supplying that step is
`single-density-expansion-forces-the-multiscale-profile`, currently **OPEN**;
until it is proved, (B3) reads as an implication whose hypothesis is N2, not as
a property of every NO base.

Suppose in addition the base carries the multiscale profile (N2) of
`lifts-over-multiscale-expanders-expand-unless-ug-value-large`:
`Phi_H(A) >= 1 - nu/24` for every `A` with `mu(A) in [1/q, tau]`, where
`tau >= 2/q` and `|V| >= q`. Since `kappa <= 1/2 < 1 - nu/24` for `nu <= 1/2`,
`mu(B) not in [1/q, tau]`, so `mu(B) > tau` or `mu(B) < 1/q`.

In the second case use the padding step of
`lifts-over-multiscale-expanders-proof`: add vertices to `B` one at a time until
the measure first reaches `1/q`, giving `B' >= B` with
`mu(B') in [1/q, 2/q] <= [1/q, tau]`. Since `e` is monotone under inclusion,

```text
mu(B)(1 - kappa) <= mu(B)(1 - Phi_H(B)) = e(B) <= e(B')
                  = mu(B')(1 - Phi_H(B')) <= (2/q)(nu/24) = nu/(12 q),
```

so `mu(B) <= nu/(12 q (1 - kappa)) <= nu/(6q) = nu delta/6`. This is (B3).

## (B4) Galois form

By `galois-unique-game-value-is-transversal-expansion` and item (5) of
`lifts-over-multiscale-expanders-proof`, in `Gal(G, K, mu)` the label-extended
graph is `Cay(G, mu)` and the base is the Schreier graph on `G/K`, with
`q = [G:K]`. For `G = F_2^N` and `K` of index `2^c` the quotient is `F_2^c` and
the base is `Cay(F_2^c, w)` with `w` the pushforward of `mu` and total mass `W`.
Its normalized adjacency eigenvalues are the characters

```text
what(a) = sum_b w_b (-1)^(a . b) / W = 1 - 2 w({b : a . b = 1})/W,
```

so `lambda_2 = min_(a != 0) 2 w({b : a . b = 1})/W`. The bound
`lambda_2 < theta` of (B2) therefore says that some `a != 0` in the dual of
`F_2^c` has `w({b : a . b = 1})/W < theta/2 = 2.5 X(eta) sqrt(eta)`. Pulling `a`
back along `G -> G/K` gives a character `chi` of `F_2^N` trivial on `K` with
`mu({g : chi(g) = -1})/W < 2.5 X(eta) sqrt(eta)`, and the hyperplane
`{x : chi(x) = 1}` has measure `1/2` and expansion exactly that quantity in
`Cay(F_2^N, mu)`. It contains `K`. This is (B4).

## Replay

The only computational content is the load-rigidity lemma feeding (B1); its
exact replay is
`python3 experiments/sse-lift-base-gate-2026-09-18/check_load_rigidity.py 1`
(56,208 sets, 0 failures, exit 0), which also checks the Rayleigh identity
`E[(f_u - f_v)^2]/(2 E[f^2]) = Phi_H(A)/(1 - mu(A))` used to pass from the
(Y-cut) branch to (Y-spec). (B0) is a citation of an established item, (B2) is a
citation of an established gate, and (B3), (B4) are two-line computations.

## What is not proved

- (B2) needs `H(x)` loop-free and regular, because both the AKKSTV import and
  load rigidity are stated there.
- (B2) says nothing about reductions that are not support-spread; that branch is
  survivor (S2) of the target claim.
- (B3) uses the N2 profile, and **N2 is not forced on the NO outputs.** (An
  earlier version of this route said it was; refereeing on 2026-09-18 corrected
  that, and the correction is what put the target claim back to OPEN.) Item (4)
  of `lifts-over-multiscale-expanders-expand-unless-ug-value-large` forces "N1 at
  level `nu` and N2 **at scale `1/q`**" — the cylinder half of its necessity item
  (3) reaches only sets of measure exactly `1/q`. N2 proper quantifies over the
  whole range `mu(A) in [1/q, tau]` and is a hypothesis of the *sufficiency*
  half (item (2)), never a consequence of the necessity half. From (B0) plus
  (B2) plus Cheeger, the only unconditional conclusion is `mu(B) != 1/q`.
  Propagating expansion from the single density `1/q` up the window is
  `single-density-expansion-forces-the-multiscale-profile` (**OPEN**, and with a
  recorded counterexample sketch against it); the naive random-halving argument
  loses a factor `k = q mu(A)` and is vacuous once `mu(A) >= 1/(eta q)`.
  Concretely, `1/rho` weakly coupled clusters of measure `rho` with
  `1/q << rho <= tau` appear to have `Phi_H(1/q) >= 1 - eta`, `lambda_2 ~ 0` and
  a sparse cut at measure `rho` inside the window. So (B3) is an implication
  under N2, and (B4) is unaffected. Nothing here forces the YES bases to satisfy
  N2 either.
- No step gives any evidence for or against `small-set-expansion-hypothesis`
  itself. The output is a shape constraint on proofs, and a decomposition.
