---
rg: 2
id: fpbs-rotation-margin-returns-one-arm-credit-proof
kind: route
title: Proof that the antipodal comparison kappa_n of the rotated FPBS slit events is sandwiched as P(L^Phi | U^Phi) <= kappa_n <= pi P(L^Phi | U^Phi) / E[rho | U^Phi], with rho the distance from the random slit angle to the bad set, so that under a margin hypothesis (K) is equivalent to the exponent bound zeta + alpha < 7/24, stronger than (ii); and that in the Poisson independent-offset model of wide components the rotated conditional decorrelation holds exactly while kappa_n decays like n^{-(alpha - 5/48)}
target: fpbs-rotation-margin-returns-one-arm-credit
requires:
  - fpbs-slit-winding-law-and-rotation-reduction
---

## 0. Setting

Everything is as in `fpbs-slit-winding-law-and-rotation-reduction`
(Sections 0-4 of its proof). Triangular site percolation at `p = 1/2` in
the wired box `B_n`, boundary cluster `I_n`, slit point `z0 = (1/2,0)`,
local event `E0`. On `E0` each pinch-free white component `W` has a lifted
argument range `J_W = [m_W, M_W]` about `z0`. For `φ ∈ R`,

    U^φ = E0 ∩ {no W and k with [φ+2kπ, φ+(2k+1)π] ⊆ J_W},
    L^φ = U^{φ+π},

so `U^0 = U_n` and `L^0 = L_n` (Theorem A there). Work on the circle
`T = R/2πZ`. On `E0` put

    B = ∪_W  ( [m_W, M_W - π] mod 2π ),

where a component with `M_W - m_W < π` contributes nothing and one with
`M_W - m_W - π >= 2π` contributes all of `T`. Then `U^φ` holds iff
`E0` holds and `φ ∉ B`. There are finitely many components, so `B` is
closed and `G = T \ B` is open. Off `E0` put `G = ∅`.

Let `g = |G|/2π` (this is `g_U` there) and `g_UL = |G ∩ (G - π)|/2π`.
Let `Φ, Ψ` be independent uniform points of `T`, independent of the
configuration `ω`. As there,

    ū_n = E g = P(U^Φ),   d̄_n = E g_UL = P(U^Φ ∩ L^Φ),
    E g^2 = P(U^Φ ∩ U^Ψ),  κ_n = d̄_n / E g^2.

Write `ᾱ`, `ζ̄` for the exponents of `ū_n`, `d̄_n` when they exist, and
`p_0 = P(E0) = n^{-5/48+o(1)}` (Theorem B there, with the lower bound
`p_0 >= P(0 ∈ I_n)`).

**The margin.** On `{Φ ∈ G}` let `ρ = dist_T(Φ, B)`, the circular
distance, with `ρ = π` if `B = ∅`. Since `B` is closed, `ρ > 0` on
`{Φ ∈ G}`.

## 1. The margin sandwich

**Lemma 1.** On `{Φ ∈ G}`, `g >= ρ/π`.

*Proof.* The open arc of radius `ρ` about `Φ` misses `B`, so it lies in
`G`. If `ρ <= π` its length is `2ρ`, so `|G| >= 2ρ`. If `B = ∅`, then
`g = 1 = ρ/π`. □

**Lemma 2.** `E g^2 = E[g ; U^Φ]`.

*Proof.* `g = P(Φ ∈ G | ω)`, and `g` is a function of `ω`. So
`E[g^2] = E[g · E[1(Φ ∈ G) | ω]] = E[g 1(Φ ∈ G)]`, and `{Φ ∈ G} = U^Φ`. □

**Theorem 1 (margin sandwich).**

    (1/π) E[ρ | U^Φ]  <=  E g^2 / ū_n  <=  1,

and therefore

    P(L^Φ | U^Φ)  <=  κ_n  <=  π P(L^Φ | U^Φ) / E[ρ | U^Φ].

*Proof.* By Lemmas 2 and 1, `E g^2 = E[g ; U^Φ] >= E[ρ/π ; U^Φ]
= ū_n E[ρ | U^Φ]/π`. Also `g^2 <= g`, so `E g^2 <= ū_n`. Divide
`d̄_n = P(U^Φ ∩ L^Φ) = ū_n P(L^Φ | U^Φ)` by `E g^2`. □

So `κ_n` is not an antipodal-versus-independent comparison in any
essential way. Up to the margin factor `π/E[ρ | U^Φ] ∈ [1, ∞)`, it *is*
the conditional probability that the lower side holds given the upper
side.

## 2. What (K) is

Consider the margin hypothesis

    (M)   E[ρ | U^Φ] >= n^{-o(1)}.

It says that a direction good at every scale is typically not squeezed to
within a polynomially small angle of a bad arc. Section 4 explains why
it is natural. It is OPEN.

**Corollary 2 (the exponent of κ).** Suppose the exponents `ᾱ`, `ζ̄`
exist.

(a) Always, `κ_n >= P(L^Φ | U^Φ) = n^{-(ζ̄ - ᾱ) + o(1)}`.

(b) Under (M), `κ_n = n^{-(ζ̄ - ᾱ) + o(1)}`.

*Proof.* `P(L^Φ | U^Φ) = d̄_n/ū_n`. Apply Theorem 1. □

**Corollary 3 ((K) is the stronger exponent bound).** Let
`0 <= δ < 7/24 - 2ᾱ`, and consider (K): `κ_n >= n^{-δ+o(1)}`.

(a) If `ζ̄ + ᾱ < 7/24`, then (K) holds with `δ = ζ̄ - ᾱ`.

(b) Under (M), (K) with any admissible `δ` implies `ζ̄ <= ᾱ + δ`, and
hence `ζ̄ + ᾱ < 7/24`.

So, under (M), "(K) for some admissible `δ`" is equivalent to

    (Σ)   ζ̄ + ᾱ < 7/24.

*Proof.* (a) By Corollary 2(a), `κ_n >= n^{-(ζ̄-ᾱ)+o(1)}`, and
`ζ̄ - ᾱ < 7/24 - 2ᾱ` is (Σ). (b) By Corollary 2(b),
`n^{-δ} <= κ_n n^{o(1)} = n^{-(ζ̄-ᾱ)+o(1)}`, so `ζ̄ - ᾱ <= δ`. □

**Corollary 4 (the rotation reduction gives nothing at exponent level).**
(Σ) implies the rotated (ii), `ζ̄ < 3/16`, directly, with room
`ᾱ - 5/48 >= 0` to spare: `ζ̄ < 7/24 - ᾱ <= 7/24 - 5/48 = 3/16`, because
`U^Φ ⊆ E0` gives `ᾱ >= 5/48`.

Theorem B of the previous node, `d̄_n >= κ_n ū_n^2/p_0`, is correct. But
under (M) its hypothesis (K) is equivalent to (Σ). That is a direct
exponent inequality for `d̄_n`, and it is *stronger* than the conclusion
`ζ̄ < 3/16` by exactly `ᾱ - 5/48`. The factor `n^{5/48}` that
Cauchy-Schwarz credits is handed back in `κ_n`. The exact bookkeeping is
Section 3.

## 3. Exact bookkeeping: the right residual quantity

Define the *rotated conditional decorrelation* and the *Cauchy-Schwarz
slack*

    R_n = d̄_n p_0 / ū_n^2 = P(U^Φ ∩ L^Φ | E0) / P(U^Φ | E0)^2,
    S_n = p_0 E g^2 / ū_n^2.

**Proposition 5.** (a) `κ_n = R_n / S_n` exactly, and `S_n >= 1`.

(b) `E[ρ | U^Φ] / (π P(U^Φ | E0)) <= S_n <= 1 / P(U^Φ | E0)`.

(c) If the exponents exist, `ζ̄ = 2ᾱ - 5/48 + r̄`, where `R_n = n^{-r̄+o(1)}`.
In particular, the rotated (ii), `ζ̄ < 3/16`, is *equivalent* to

    (R)   R_n >= n^{-δ}  for some  δ < 7/24 - 2ᾱ.

(d) Under (M), `S_n = n^{ᾱ - 5/48 + o(1)}`. So (K) is (R) with the extra
factor `n^{ᾱ - 5/48}` demanded on top.

*Proof.* (a) The identity is algebra. `g = 0` off `E0`, so by
Cauchy-Schwarz `ū_n^2 = (E[g ; E0])^2 <= p_0 E g^2`. (b) The lower bound
is Theorem 1: `E g^2 >= ū_n E[ρ|U^Φ]/π`, and `p_0/ū_n = 1/P(U^Φ|E0)`. The
upper bound is `E g^2 <= ū_n`. (c) `d̄_n = R_n ū_n^2/p_0`; take
exponents, using `p_0 = n^{-5/48+o(1)}`. Then `ζ̄ < 3/16` iff
`r̄ < 3/16 + 5/48 - 2ᾱ = 7/24 - 2ᾱ`. (d) Use (b) with
`P(U^Φ|E0) = n^{-(ᾱ-5/48)+o(1)}`. □

So Theorem B, `d̄_n >= κ_n ū_n^2/p_0`, is the identity
`d̄_n = R_n ū_n^2/p_0` with `R_n` replaced by the smaller `R_n/S_n`. The
admissible range `δ < 7/24 - 2ᾱ` is exactly right for `R_n`, the
quantity that is naturally of order one. Putting it on `κ_n` costs the
slack `S_n`, which is polynomially large as soon as `ᾱ > 5/48`. The
correct target of the rotation route is (R), not (K).

## 4. The Poisson independent-offset model

The mechanism can be computed exactly in the following model. It is the
heuristic picture of wide components at separated scales: each scale
contributes a wide component independently, with an argument offset that
is uniform by rotation invariance of the scaling limit. Work conditionally
on `E0`. The *bad arcs* `[m_W, M_W - π]` have normalised length
`x_W = (M_W - m_W - π)/2π`. Assume:

(P) the pairs (offset `m_W/2π mod 1`, length `x_W`) form a Poisson point
process on `T_1 × (0, 1/2)` (with `T_1 = R/Z`), of intensity
`dθ ⊗ ν(dx)`, where `ν` is finite with mass `Λ`. Put `I = ∫ x ν(dx)`.

**Proposition 6.** In model (P):

(a) `P(U^Φ | E0) = e^{-I}` and `P(U^Φ ∩ L^Φ | E0) = e^{-2I}`. Hence
`R_n = 1` exactly.

(b) `E[g^2 | E0] = 2 ∫_0^{1/2} exp(-∫ (x + min(x,s)) ν(dx)) ds`.

(c) `e^{-I} <= κ_n <= e^{-I} (Λ/2)/(1 - e^{-Λ/2})`.

(d) For `0 <= τ <= 1/4`, `P(ρ > 2πτ | U^Φ) = e^{-2τΛ}`. Hence
`E[ρ | U^Φ] >= π(1 - e^{-Λ/2})/Λ`.

*Proof.* Fix the point `Φ = φ`. An arc `[θ, θ + x]` (normalised) covers
`φ` iff `θ ∈ [φ - x, φ]`, which is a set of measure `x`. So the number of
arcs covering `φ` is Poisson with mean `I`, which proves the first formula
of (a). Since `x < 1/2`, no arc covers both `φ` and `φ + 1/2`. So the
arcs covering `φ` and those covering `φ + 1/2` come from disjoint regions
of `T_1 × (0,1/2)`, and the number covering either is Poisson with mean
`2I`. This proves the second formula of (a).

(b) For points at normalised distance `s ∈ [0, 1/2]`, the offsets whose
arc covers both form a set of measure `(x - s)^+`, since `x < 1/2 <= 1 - s`
rules out wrap-around. So the offsets whose arc covers at least one of
them form a set of measure `2x - (x-s)^+ = x + min(x,s)`. Then average
over `s`, which is uniform on `[0, 1/2]` when `Φ, Ψ` are independent
uniform.

(c) We have `κ_n = e^{-2I}/E[g^2|E0]`. Since `min(x,s) >= 0`,
`E[g^2|E0] <= e^{-I}`, which gives the lower bound. Since `min(x,s) <= s`,
`∫ min(x,s) dν <= sΛ`, so
`E[g^2|E0] >= e^{-I} · 2∫_0^{1/2} e^{-sΛ} ds = e^{-I}(2/Λ)(1 - e^{-Λ/2})`.

(d) Arcs meeting `[φ - τ, φ + τ]` have offsets in a set of measure
`x + 2τ <= 1`. Removing the offsets that cover `φ` leaves a disjoint set
of measure `2τ`. So, given that `φ` is uncovered, the absence of the
remaining arcs has probability `e^{-2τΛ}`. Integrate `P(ρ > 2πt | U^Φ)`
over `t ∈ [0, 1/4]`. □

**Reading.** In model (P), with `Λ = n^{o(1)}` (at most `O(log n)` scales
carry wide components):

* The rotated (ii) holds iff `ζ̄ = 2ᾱ - 5/48 < 3/16`, i.e. `ᾱ < 7/48`.
* (M) holds, by (d).
* But `κ_n = n^{-(ᾱ - 5/48) + o(1)}` does *not* tend to a positive
  constant: it carries the full conditional one-sided cost
  `P(U^Φ|E0)`.
* (K) with `δ = ᾱ - 5/48` needs `ᾱ - 5/48 < 7/24 - 2ᾱ`, i.e.
  `ᾱ < 19/144`, which is strictly stronger than `ᾱ < 7/48`.

So, even in the most favourable independent picture, (K) as a
decorrelation statement with `δ -> 0` is *false*. It is only true as an
exponent inequality that is at least as strong as the goal. The quantity
that is exactly 1 in the model is `R_n`.

**Fixed-count defect.** Suppose instead that there are exactly `N` arcs
with lengths `x_1, …, x_N` and iid uniform offsets, as in the toy model of
the previous node. Then `P(U|E0) = Π(1 - x_i)` and
`P(U ∩ L|E0) = Π(1 - 2x_i)`, so

    R_n = Π_i (1 - x_i^2/(1 - x_i)^2).

Poissonisation removes this defect exactly. In the fixed-count model,
`R_n = n^{-o(1)}` iff `Σ_i x_i^2/(1-x_i)^2 = o(log n)` (for lengths bounded
away from `1/2`). So `R_n` probes the *second moment* of the wide-arc
lengths, not their first moment `I`, which sets `P(U|E0)`.

## 5. Numerics (NUMERICAL)

The code is `experiments/fpbs-rotation-margin-2026-09-19/margin.c`, which
extends the previous node's `wind.c`. The angle is discretised to 720
bins. We ran `T = 20000` samples for `n = 8, 16, 32`, 10000 for `n = 64`,
4000 for `n = 128` and 800 for `n = 256`. There were zero winding-law
violations. Write `N` for the number of wide components, those with
`M_W - m_W > π`.

    n    p0     ū      d̄      κ      P(L|U) R_n    S_n    E[ρ|U] E[N|E0] P(N>=2|E0)
    8   .6958  .6820  .6682  .9953  .9797  .9996  1.0043  2.931  .166   .0001
    16  .6533  .6320  .6108  .9915  .9664  .9991  1.0076  2.823  .232   .0009
    32  .6022  .5736  .5453  .9865  .9507  .9981  1.0118  2.704  .306   .0039
    64  .5643  .5304  .4974  .9824  .9377  .9976  1.0155  2.601  .372   .0099
    128 .5222  .4832  .4453  .9770  .9216  .9960  1.0195  2.498  .433   .0153
    256 .4850  .4391  .3956  .9698  .9007  .9948  1.0258  2.361  .521   .036

Here `P(N>=2|E0)` is estimated as `(E N^2 - E N)/2p_0`, which is exact
when `N <= 2`. The "surrogate" lines of `results.txt` redraw the offsets
of the wide arcs uniformly, keeping their lengths (8 copies per sample).
They reproduce `ū`, `d̄`, `E g^2` and `R_n` to within `2·10^-4`, and
`E[ρ 1_U]` to within `1.5·10^-3`, at every `n`.

Local exponents over `8 -> 256`, from five doublings:

* `κ_n`: 0.0075.
* `R_n`: 0.0014.
* `S_n`: 0.0061.
* `P(L|U) = d̄/ū`: 0.024.

These satisfy `κ = R/S` term by term. The margin `E[ρ|U]` stays at order
one, but it falls slowly as `E[N|E0]` grows. That is consistent with
Proposition 6(d), where `E[ρ|U] ≈ π/(1+Λ)`.

**Interpretation.** At these sizes `E[N|E0] <= 0.52`, and two wide
components are rare. So the sample is in the one-hole regime.

* There `E g^2/ū` is still near 1, because a single arc barely reduces
  `g`. This hides most of the decay of `P(L|U)` from `κ_n`. The measured
  `δ̄ ≈ 0.007` is therefore pre-asymptotic.
* Corollary 2 predicts that the asymptotic exponent of `κ_n` is
  `ζ̄ - ᾱ`, estimated here at about 0.024.
* `R_n` is the one quantity whose deficit is both small and not growing
  polynomially fast (0.0014). This matches Proposition 6.

## 6. What is left

1. **(R), the rotated conditional decorrelation:**
   `P(U^Φ ∩ L^Φ | E0) >= n^{-δ} P(U^Φ|E0)^2` with `δ < 7/24 - 2ᾱ`. By
   Proposition 5(c) it is equivalent to the rotated (ii).

   By the winding law, a wide component blocks `U^φ` or `L^φ` but never
   both, since its bad arc is shorter than `π` whenever
   `M_W - m_W < 2π`; components with range at least `2π` kill both, and
   are confined to `E0 \ W_2π`. So (R) follows from:

   (R1) approximate independence, given `E0`, of the angular offsets of
   wide components at well-separated scales, with multiplicative error
   `n^{-o(1)}` (quasi-multiplicativity for the outermost white arms
   around the slit); and

   (R2) `E[Σ_W x_W^2 | E0]` and `P(E0 \ W_2π | E0)` being small enough
   that the fixed-count defect of Section 4 is `n^{-o(1)}`.

   Neither is proved. (R1) is the substantive input.

2. **(T): `P(D'_n(0)) >= n^{-o(1)} d̄_n`.** This is untouched here. It
   needs the axis direction not to be atypical among all directions,
   which is rotation invariance at the level of exponents.

3. **The goal (ii) needs `ᾱ < 7/48` on this route**, even with (R) and
   (T) proved. The numerics give `ᾱ ≈ 0.12 < 7/48 ≈ 0.146`, but no bound
   `ᾱ < 7/48` is proved. Such a bound is again an exponent bound for a
   one-sided slit event.

**Dead route.** "Prove `κ_n >= n^{-o(1)}` by coupling the angular
positions of wide components." It is false in the model where that
coupling is exact (Proposition 6(c)), and in general it would imply (Σ),
which is stronger than the goal (Corollary 3).
