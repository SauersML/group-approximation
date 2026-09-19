---
rg: 2
id: fpbs-rotation-margin-returns-one-arm-credit
kind: claim
title: The antipodal ratio kappa_n of the rotated FPBS slit events equals P(L^Phi | U^Phi) up to a margin factor, so the rotation reduction's hypothesis (K) hands back the one-arm credit n^{5/48}; the correct residual is the rotated conditional decorrelation R_n = dbar_n P(E0)/ubar_n^2, which is exactly 1 in the Poisson independent-offset model
distinct_from:
  fpbs-slit-winding-law-and-rotation-reduction: that proves the winding law and the Cauchy-Schwarz rotation reduction and leaves the antipodal ratio kappa_n as the gap; this sandwiches kappa_n between P(L|U) and a margin multiple of it, shows the hypothesis (K) on kappa_n is circular (it hands back the one-arm credit), and replaces it by the conditional decorrelation R_n, which is exact in a Poisson offset model
artifacts:
  - research/fpbs-rotation-margin-returns-one-arm-credit-proof.md
  - experiments/fpbs-rotation-margin-2026-09-19/margin.c
  - experiments/fpbs-rotation-margin-2026-09-19/run_all.sh
  - experiments/fpbs-rotation-margin-2026-09-19/results.txt
---

**Status.** Theorem 1 and Corollaries 2-4 and Propositions 5-6 are
ESTABLISHED (full proofs). The (K) route is an OBSTRUCTION: under the
margin hypothesis (M) it is circular, and in model (P) it is false as a
decorrelation. (M) itself, the target (R) and the transfer (T) are OPEN.
The tables are NUMERICAL. Proofs are in
`fpbs-rotation-margin-returns-one-arm-credit-proof.md`.

## Setting

We use the notation of `fpbs-slit-winding-law-and-rotation-reduction`.

* On `E0`, the bad set is `B = ∪_W [m_W, M_W - π] mod 2π` and the good
  set is `G = T \ B`.
* `g = |G|/2π`, `ū_n = E g`, `d̄_n = P(U^Φ ∩ L^Φ)`, and
  `κ_n = d̄_n/E g^2`.
* The margin is `ρ = dist(Φ, B)` on `U^Φ = {Φ ∈ G}`.

## Results

**Theorem 1 (margin sandwich).**
`(1/π) E[ρ|U^Φ] <= E g^2/ū_n <= 1`. Hence

    P(L^Φ|U^Φ) <= κ_n <= π P(L^Φ|U^Φ)/E[ρ|U^Φ].

The proof uses only `g >= ρ/π` on `U^Φ` and `E g^2 = E[g; U^Φ]`.

**Corollaries 2-4.** Under (M), `E[ρ|U^Φ] >= n^{-o(1)}`:

* `κ_n = n^{-(ζ̄-ᾱ)+o(1)}`.
* (K), that is `κ_n >= n^{-δ}` for some `δ < 7/24 - 2ᾱ`, is equivalent to
  (Σ): `ζ̄ + ᾱ < 7/24`. The direction (Σ) ⇒ (K) holds unconditionally.
* (Σ) implies `ζ̄ < 3/16` directly, with room `ᾱ - 5/48 >= 0` to spare.

So the rotation reduction gains nothing at the exponent level: the credit
`n^{5/48}` from Cauchy-Schwarz is paid back in `κ_n`.

**Proposition 5 (bookkeeping).** Define

    R_n = P(U^Φ∩L^Φ|E0)/P(U^Φ|E0)^2,
    S_n = p_0 E g^2/ū_n^2 >= 1.

Then:

* `κ_n = R_n/S_n` exactly.
* `ζ̄ = 2ᾱ - 5/48 + r̄`, where `R_n = n^{-r̄+o(1)}`.
* The rotated (ii), `ζ̄ < 3/16`, is equivalent to
  (R): `R_n >= n^{-δ}` for some `δ < 7/24 - 2ᾱ`.
* Under (M), `S_n = n^{ᾱ-5/48+o(1)}`.

**Proposition 6 (Poisson model (P)).** Take wide arcs to be Poisson with
uniform offsets, lengths `x < 1/2` and finite mass `Λ`, and put
`I = ∫x dν`. Then:

* `R_n = 1` exactly.
* `e^{-I} <= κ_n <= e^{-I}(Λ/2)/(1-e^{-Λ/2})`.
* `E[ρ|U^Φ] >= π(1-e^{-Λ/2})/Λ`.

So (M) holds, but `κ_n` decays like `P(U^Φ|E0)`. The rotated (ii) needs
`ᾱ < 7/48`, while (K) needs `ᾱ < 19/144`.

With a fixed count of arcs, `R_n = Π(1 - x_i^2/(1-x_i)^2)`: the only
defect is second order.

## Numerics

Section 5 of the proof has the tables for `8 <= n <= 256`. `R_n` stays
within 1% of 1. `E[ρ|U^Φ]` stays at order one. Two wide components are rare
(`P(N>=2|E0) <= 0.04`), so the uniform-offset surrogate agrees
with the data to within noise. The measured slow decay of `κ_n` is
pre-asymptotic, and is carried by `P(L|U)`.

## What is left

The rotation route to (ii) and (H) now needs:

* (R): the conditional decorrelation of the upper and lower rotated slit
  events given `E0`, polynomially weaker than order one. This is not (K).
* (T): `P(D'_n(0)) >= n^{-o(1)} d̄_n`.

Proposition 6 identifies the mechanism for (R). By the winding law each
wide component blocks at most one of `U^φ` and `L^φ`. So (R) reduces to
approximate independence of the angular offsets of wide components across
scales, *conditionally on E0*, together with `Σ x_W^2 = o(log n)`. This
is a quasi-multiplicativity statement for the angular positions of the
outermost white arms at the slit.
