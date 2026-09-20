---
rg: 2
id: houghton-ray-stabilizer-corridor-bounds-cap-near-quadratic
kind: claim
title: "For n >= 4, Y-corridor lower bounds over the one-ray stabilizer H_(n-1) certify at most x^2 log x; the forced-commutator family behind the cubic H_3 bound certifies only x^2"
distinct_from:
  houghton-cohomological-dehn-lower-bounds-cap-at-quadratic: that kills cocycle and central-extension certificates; this kills corridor-length certificates of the ascending HNN splitting H_n = H_(n-1) *_φ, a different class. The cubic H_3 bound is a corridor certificate, not a cocycle one.
  houghton-group-h3-has-at-least-cubic-dehn-function: that is the n = 3 corridor lower bound, which works; this shows the same argument cannot give more than x^2 log x for any n >= 4, and pins down the step where it dies.
  houghton-ray-stabilizer-distortion-at-most-x-log-x: that is the distortion input; this is its consequence for Dehn lower-bound methods.
---

Fix `n >= 4`. Take:

- `K ≅ H_(n-1)`, the pointwise stabilizer of ray `n`;
- `Y = λ_(1,n)`;
- `φ(h) = Y h Y^(-1)`, which maps `K` into `K`.

Then `H_n = K *_φ` is an ascending HNN extension. It has a finite presentation

`P_n = <S_K, Y | R_0 ∪ {Y s Y^(-1) φ(s)^(-1) : s ∈ S_K}>`

with `R_0` a finite set of `Y`-free relators, and `φ(s)` a fixed `S_K`-word.
Let `σ_P` be the longest cell side, i.e. the maximum of `1` and the lengths
`|φ(s)|`.

In a van Kampen diagram `Δ` over `P_n` for a word `w`, the `Y`-corridors pair
the `Y`-letters of `w`. Each pair `(i, j)` has an arc `w(i, j)`, which lies in
`K`, and a corridor of length at least `|w(i, j)|_(S_K) / σ_P`.

A **corridor certificate** is any lower bound of the form

`Area(w) >= min over admissible pairings Π of Σ_((i,j) ∈ Π) F(w(i, j))`,

where `F(h) <= A |h|_(S_K) + B`.

The `n = 3` cubic proof is of this form, with `F = inv <= |·|_(S_K)`.

**Claim.**

- **(A) Class cap.** For `n >= 4`, every corridor certificate satisfies
  `Cert(x) := max_(|w| <= x) (the bound for w) <= C x^2 log x`.
  More precisely, `Cert(x) <= (A x / 2) Dist_K(x) + B x`, and
  `Dist_K(x) ≼ x log x` by `houghton-ray-stabilizer-distortion-at-most-x-log-x`.
- **(B) Forced family.** For every `S_K`-word `u` and `m >= 2`,
  `W = [Y^m u Y^(-m), α]` is null-homotopic, and its admissible matching is
  forced as in the `n = 3` proof. The certified value is
  `(2/σ_P) Σ_(k<m) |φ^k(u)|_(S_K)`.
  For `n >= 4`, **lid transport** gives
  `|φ^k(u)|_(S_K) <= C (|u| + k)`, so this family certifies at most
  `C |W|^2`.

**Where every member dies.** The invariant is the `K`-length of corridor
arcs, which is controlled by the distortion of `H_(n-1)` in `H_n`. The step
that fails is the cost inequality `ℓ >= |arc|_K / σ_P`. Once `K` has a third
ray, the arc elements are cheap in `K`:

- by lid transport, `φ^k(σ) = z^(-1) σ z` with `z` a short word that parks
  the lid on a spare ray;
- by three-stack merge sort, in general.

For `n = 3`, `K = H_2` has two rays, and both tricks fail. That is why `H_3`
gets `x^3`.

**What survives.** A superquadratic lower bound for some `H_n` with `n >= 4`
needs a method outside this class. Either:

- lower-bound the area of the `Y`-free complementary regions using
  `δ_(H_(n-1))` (for `n = 4`: do the cubic `H_3` words stay cubic inside
  `H_4`?); or
- use a different splitting or invariant.

A corridor argument alone gains at most the log factor, and only if `K` is
genuinely `x log x`-distorted.

## Attempts

- 2026-09-19 (swarm-0917-w14-w14-z-follow, host-geometry): proved in
  `houghton-ray-stabilizer-corridor-cap-proof`. Machine checks for `n = 4, 5`
  in `experiments/houghton-lid-transport-2026-09-17/check_lid_and_sort.py`:
  - `φ` preserves `K`;
  - the lid lemma, on random finitary `σ`;
  - the translation-conjugation identity;
  - the forced matching, for random `u`.
