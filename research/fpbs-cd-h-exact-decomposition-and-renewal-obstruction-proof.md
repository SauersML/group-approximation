---
rg: 2
id: fpbs-cd-h-exact-decomposition-and-renewal-obstruction-proof
kind: route
title: Proof that the FPBS axis-to-axis box event is the intersection of two increasing reflected half-plane events whose one-arm parts are the half-plane K-arm events, of the one-site flip bound P(D'_n(0)) <= 2 P(D'_n(0) ∩ C_n), of the reformulation of (ii) and (CD_H) as correlation-gain exponents, and of the independent-scales model showing that FKG, reflection and quasi-multiplicativity cannot give (CD_H)
target: fpbs-cd-h-exact-decomposition-and-renewal-obstruction
requires:
  - fpbs-box-event-quadrant-k-arm-reduction
---

## 0. Setting

Notation is as in `fpbs-box-event-quadrant-k-arm-reduction` (Section 0
there). Triangular site percolation at `p = 1/2` in axial coordinates
`(i,j)`, with unit steps `d_0..d_5 = (1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)`.
The box `B_n` is wired: its boundary sites lie in the black cluster `I_n`
of `∂B_n`. Colour a site *white* if it is not in `I_n`, whatever its
Bernoulli colour. A step `c -> c + d_k` is a *pinch* if both common
neighbours `c + d_{k±1}` lie in `I_n` or outside `B_n`. A *white path* is
a path of white sites of `B_n` with no pinch step. Write
`S_n = {(i,0) : -n < i <= 0}` and `P_n = {(i,0) : 1 <= i <= n-1}`, the
interior sites of the positive axis. Then `D'_n(0)` is the event that no
white path joins `S_n` to `P_n`. The boundary sites `(n,0)` and `(-n,0)`
are in `I_n`, so it makes no difference whether they are included.
Always `n >= 2`.

For `s = +1` let `H^+ = {j >= 0}`, and for `s = -1` let `H^- = {j <= 0}`.
Define

    U_n = { no white path with all sites in H^+ joins S_n to P_n },
    L_n = { no white path with all sites in H^- joins S_n to P_n }.

The pinch condition in `U_n` refers to the *global* cluster `I_n`,
including sites with `j < 0`.

## 1. Theorem A

**Lemma 1.1 (monotonicity).** `I_n` is increasing in the configuration.
The set of white sites is decreasing. The set of pinch steps is
increasing. Hence every event of the form "no white path in a fixed site
set `V` joins `X` to `Y`" is increasing. In particular `U_n`, `L_n` and
`D'_n(0)` are increasing.

*Proof.* Adding black sites can only merge clusters into the boundary
cluster. Whether a step is a pinch is an increasing condition on `I_n`.
So after raising the configuration, every white path is still a path of
sites that were white before, through steps that were not pinches before.
The set of white paths shrinks, and the absence of a white path is
preserved. ∎

**Lemma 1.2 (reflection).** The map `R(i,j) = (i+j,-j)` of the previous
step's Lemma 1.2 fixes `S_n` and `P_n` pointwise, exchanges `H^+` and
`H^-`, maps pinch steps to pinch steps, and preserves the measure. Hence
`R` maps `U_n` to `L_n`, and `P(U_n) = P(L_n)`.

*Proof.* `R` fixes the real axis pointwise and permutes the unit steps. It
maps common neighbours to common neighbours, `B_n` to `B_n` and `I_n` to
the `I_n` of the reflected configuration. ∎

**Proposition 1.3.** `D'_n(0) = U_n ∩ L_n`.

*Proof.* A white path in `H^+` or in `H^-` is a white path, so
`D'_n(0) ⊆ U_n ∩ L_n`. Conversely, let `v_0, ..., v_m` be a white path
from `S_n` to `P_n`. Let `m'` be its first index in `P_n`, and let
`r < m'` be the last index before `m'` in `S_n`. The real-axis sites of
`B_n` are `S_n`, `P_n`, and the two boundary sites `(±n,0)`, which are not
white. So `v_{r+1}, ..., v_{m'-1}` lie off the real axis. A unit step
changes `j` by at most one, so these sites all have the same sign of `j`.
If `m' = r + 1`, the sub-path lies on the axis. In either case the
sub-path `v_r, ..., v_{m'}` is a white path from `S_n` to `P_n` inside
`H^+` or inside `H^-`, so `U_n` or `L_n` fails. ∎

**Proposition 1.4.** `A_n(UH) = C_n ∩ U_n`, and, by Lemma 1.2,
`A_n(LH) = C_n ∩ L_n`.

*Proof.* (`⊆`) `A_n(UH) ⊆ C_n` holds by definition. Suppose `A_n(UH)`
holds and that `P = (v_0, ..., v_m)` is a white path in `H^+` from `S_n`
to `P_n`. As in Proposition 1.3, pass to the sub-path `P'` from its last
visit `s = v_r` to `S_n` before its first visit `v_{m'}` to `P_n`. Here
`s` is not the origin, which lies in `I_n`. So `s` lies in the open
segment `(-n, 0)`, and `v_{m'}` lies in `(0, n)`. Now `P'` lies in
`Q = UH ∩ hull(B_n)`, and apart from its endpoints it lies in the
interior of `Q`. It avoids `∂hull(B_n)` because its sites are not
boundary sites and `Q` is convex.
The K-arm `G` of `A_n(UH)` runs in `Q` from `0` to a point `b` of the
upper outer arc. The four points `0, s, b, v_{m'}` occur in this cyclic
order on `∂Q`. By the crossing lemma (Lemma 2.2 of the previous step) the
curves of `G` and `P'` meet, and Lemma 2.1 there says they cannot. This is
exactly the proof of Theorem 2.3(b) of the previous step. That proof uses
only the half of the white path lying on the side of the arm.

(`⊇`) Assume `C_n ∩ U_n`. Use the zigzag upper half `T` of `B_n` and the
triangulation `Γ^+` of `T` from the proof of Theorem 2.5 of the previous
step. It is obtained by flipping every checkerboard rhombus that lies
entirely in `T`. Its black edges are K-steps. Its white edges are white
steps that are not pinches, together with some white real-axis edges
whose checkerboard rhombus sticks out of `T`. Cut `∂T` into the four arcs
`A1 = {0}` (black, on `C_n`), `A2 = P_n`, `A3 = ∂B_n ∩ H^+` (black) and
`A4 = S_n \ {0}`. By the Hex lemma, either a black `Γ^+` path joins `A1`
to `A3`, or a white `Γ^+` path joins `A2` to `A4`. In the first case it
is a K-path in `UH` from `0` to `∂B_n`, so `A_n(UH)` holds. In the second
case, take the sub-path from its last site in `A4` to its next site in
`A2`. Its interior sites are off the axis. Its first and last steps join
an axis site to an off-axis site. Axis sites of the two arcs are never
adjacent, since `(-1,0)` and `(1,0)` are not neighbours. So the sub-path
uses no real-axis edge, and each of its edges is a non-pinch white step.
It is therefore a white path in `H^+` from `S_n` to `P_n`, which
contradicts `U_n`. ∎

**Theorem A** follows from Lemmas 1.1-1.2 and Propositions 1.3-1.4.
Intersecting gives
`D'_n(0) ∩ C_n = C_n ∩ U_n ∩ L_n = A_n(UH) ∩ A_n(LH)`, which is Theorem
2.5 of the previous step.

*Remark 1.5.* `U_n` and `L_n` depend on the configuration only through
the set `I_n`. Both the white sites and the pinch steps are functions of
`I_n`. So is `C_n`. Everything below concerns the law of the single
random set `I_n`.

## 2. Theorem B

**Lemma 2.1 (local forcing).** On `U_n`, one of the following holds:
`0 ∈ I_n`; or `(1,0) ∈ I_n`; or both `(0,1) ∈ I_n` and `(1,-1) ∈ I_n`. The
same holds on `L_n`, with the same three alternatives, because they are
invariant under `R`.

*Proof.* Suppose `0` and `(1,0)` are both white. The common neighbours of
`0` and `d_0 = (1,0)` are `d_1 = (0,1)` and `d_5 = (1,-1)`. If they are not
both in `I_n`, the one-step path `0 -> (1,0)` is a white path in `H^+`
from `S_n` to `P_n`, since `n >= 2`. So `U_n` fails. For `L_n`, note that
`R` fixes `(0,0)` and `(1,0)` and swaps `(0,1)` with `(1,-1)`. ∎

**Proposition 2.2 (one-site flip).** Let `E ⊆ U_n ∪ L_n` be increasing.
Then `P(E ∩ C_n^c) <= P(E ∩ C_n)`, and hence `P(E) <= 2 P(E ∩ C_n)`. At a
general density `p` the factor is `1 + (1-p)/p`.

*Proof.* Let `ω ∈ E` with `0 ∉ I_n(ω)`. By Lemma 2.1 some neighbour of
`0` lies in `I_n(ω)`. So `0` is Bernoulli-white in `ω`: were it black, it
would be joined to that neighbour and lie in `I_n`. Let `ω'` be `ω` with
`0` turned black. Then `ω' ∈ E`, because `E` is increasing. Also
`0 ∈ I_n(ω')`, because `I_n(ω) ⊆ I_n(ω')` contains a neighbour of the
black site `0`. The map `ω -> ω'` is injective on `{ω(0) = white}`. At
`p = 1/2` it preserves the probability of each configuration, and in
general it multiplies it by `p/(1-p)`. ∎

This applies to `E = U_n` and to `E = D'_n(0) = U_n ∩ L_n`. So

    P(A_n(UH)) <= P(U_n) <= 2 P(A_n(UH)),
    P(D'_n(0) ∩ C_n) <= P(D'_n(0)) <= 2 P(D'_n(0) ∩ C_n).     (2.1)

In particular, conditioning on the one-arm event costs at most a
factor 2 in (ii). The one-arm event is not an extra constraint on the box
event: it is forced up to a flip of one site.

## 3. Theorem C: what (ii) and (CD_H) say

Write `a_n = P(A_n(UH)) = P(A_n(LH))`, `c_n = P(C_n)`, `u_n = P(U_n)`,
`b_n = P(A_n(UH) ∩ A_n(LH)) = P(D'_n(0) ∩ C_n)` and `d_n = P(D'_n(0))`.
Let

    kappa_H(n) = b_n c_n / a_n^2,        rho_n = d_n / u_n^2.

FKG for the increasing events `U_n` and `L_n` gives `rho_n >= 1`. By
(2.1), `a_n <= u_n <= 2 a_n` and `b_n <= d_n <= 2 b_n`, so

    rho_n c_n / kappa_H(n) = (d_n / b_n) (a_n / u_n)^2  ∈  [1/4, 2].     (3.1)

Let `zeta(0) = limsup -log d_n / log n`. Suppose the exponents
`alpha_H = lim -log a_n / log n` and `lim -log c_n / log n = 5/48`
exist; the second is the one-arm exponent. Put
`delta_H = limsup -log kappa_H(n) / log n`. Then
`-log d_n = -log b_n + O(1) = -log kappa_H(n) + (2 alpha_H - 5/48 + o(1)) log n`,
so

    zeta(0) = 2 alpha_H - 5/48 + delta_H.                     (3.2)

(ii) says `zeta(0) < 3/16`, which is `delta_H < 3/16 + 5/48 - 2 alpha_H = 7/24 - 2 alpha_H`.
(CD_H) says `delta_H <= 0`, which is `zeta(0) <= 2 alpha_H - 5/48`.
In terms of `rho`, since `u_n = a_n n^{o(1)}` by (2.1),
`-log d_n = -log rho_n + (2 alpha_H + o(1)) log n`. So (ii) holds iff
`liminf log rho_n / log n > 2 alpha_H - 3/16`. That is:

> **(ii) is exactly the statement that the two increasing half-plane events
> `U_n`, `L_n` beat FKG by a polynomial factor `n^{2 alpha_H - 3/16 + eps}`.**

(CD_H) is the statement that they beat it by the full inverse one-arm
probability `n^{5/48 - o(1)}`. With the measured `alpha_H = 0.127`, the
first needs a gain exponent above `0.067`. The second predicts `0.104`.

This makes precise the part (d) obstruction of the previous step. A plain
FKG product is the case of gain exponent `0`. It gives `zeta(0) <= 2 alpha_H`,
and since `alpha_H >= 5/48`, this is at least `5/24`. ∎

## 4. Theorem D: the structural obstruction

Fix `p ∈ (0,1)` and `K >= 1`. On `{0,1}^{2K}` with product Bernoulli(`p`)
measure and coordinates `y_1, z_1, ..., y_K, z_K`, let

    C = ∩_k {y_k = 1 or z_k = 1},   U' = ∩_k {y_k = 1},   L' = ∩_k {z_k = 1}.

The model has every structural property used in Sections 1-3, and every
property that the proposed Kesten-Nolin program would use:

1. `C`, `U'` and `L'` are increasing, so FKG holds.
2. The involution `y <-> z` preserves the measure, fixes `C`, and swaps
   `U'` and `L'` (reflection, Lemma 1.2).
3. The arm events `A^+ = C ∩ U' = U'` and `A^- = L'` lie in the one-arm
   event, and so does every `E ⊆ U' ∪ L'`. So the flip bound of Theorem B
   holds with constant 1, and `D' := U' ∩ L'` satisfies Theorem A's
   identity `D' ∩ C = A^+ ∩ A^-`.
4. The scale `k` plays the role of the annulus `B_{2^{k+1}} \ B_{2^k}`,
   with `K = log_2 n`. All four events are intersections of independent
   per-scale events, so quasi-multiplicativity and arm separation hold
   with constant 1. The measure conditioned on `C` is again a product
   over scales. This is the exact analogue of the circuit Markov
   property: the analogue of `C` at scale `k` does not constrain the
   other scales.

Yet

    rho = P(U' ∩ L') / (P(U') P(L')) = p^{2K} / p^{2K} = 1,
    kappa = P(U' ∩ L') P(C) / (P(U') P(L')) = (2p - p^2)^K = n^{-delta},

with `delta = -log_2(2p - p^2) > 0`. For `p = 1/2`, `kappa = (3/4)^K` and
`delta = 0.415`. The one-arm probability `P(C) = (2p - p^2)^K` decays
polynomially, like the true one, and the gain `rho` is identically `1`.
Replacing `C` by `∩ {x_k = 1}` and the arms by `∩ {x_k = y_k = 1}`, with
a third coordinate, gives `kappa = 1` instead. Using the first construction at the
scales `k <= theta K` and the second at the others keeps every property
above and gives `delta = theta (-log_2(2p - p^2))`. So every value in
`[0, 0.415]` occurs at `p = 1/2`.

**Consequence.** No argument that uses only monotonicity, FKG,
reflection symmetry, the flip bound, independence across scales,
quasi-multiplicativity or arm separation, with any constants, can prove
(CD_H). Such an argument cannot even prove the weak gain (ii) needs, since
the model has `rho = 1`. The value of `delta_H` is a genuine exponent of
the lattice model. It measures how often, at a typical scale, the upper
and lower K-arms pay for the one-arm crossing *jointly* rather than
separately. ∎

## 5. The (CD_H) route under one-arm conditioning: where it dies (DEAD END)

The brief proposed proving (CD_H) by arm separation and
quasi-multiplicativity under one-arm (IIC-type) conditioning, in the style
of Kesten and Nolin. Written out, the program has three steps.

1. *Quasi-multiplicativity* for the three events `C`, `A^+ = A(UH)` and
   `A^+ ∩ A^-`: `P(E_n) ≍ P(E_m) P(E_{m,n})` with annulus versions
   `E_{m,n}`. This needs arm separation for K-arms, whose jumps cross pinch
   edges. It is plausible, and the upper half is easy. Given that a black
   circuit of `I_n` surrounds `B_m`, the interior is independent of the
   exterior, and `U_n` and `L_n` split into inner and outer parts, because
   white paths cannot cross a K-path (Lemma 2.1 of the previous step).
2. *Renewal.* Iterating over the `log_2 n` dyadic annuli gives
   `kappa_H(n) = ∏_k kappa_k`, up to a factor between `c^{log_2 n}` and
   `c^{-log_2 n}`. Here `kappa_k` is the annulus decorrelation factor at
   scale `2^k`, and step 1 gives `kappa_k ∈ [c, 1/c]` for a constant
   `c > 0`. The error is already polynomial in `n`, so step 2 can identify
   `delta_H` only up to `O(log(1/c))`.
3. *Decorrelation.* One needs `∏_k kappa_k >= n^{-o(1)}`, that is, the
   factors `kappa_k` tend to `1` in Cesàro mean.

**The route dies at step 3.** Steps 1 and 2 turn (CD_H) into the statement
that a scale-invariant annulus quantity equals `1` in the limit. That is a
statement about the value of an exponent. Theorem D shows it is not a
consequence of any of the structure that steps 1 and 2 use. The toy model
satisfies steps 1 and 2 with constant `1` and has `kappa_k = 2p - p^2`
at every scale. So separation plus quasi-multiplicativity yield only
`kappa_H >= n^{-C}` with a constant `C` of unknown size, which is the
trivial FKG bound up to the value of `C`.

**The shortcut through conditional FKG is false.** If `P( · | C_n)` were
positively associated on the increasing events `U_n` and `L_n`, then
`kappa_H >= 1` and (CD_H) would follow at once. Exhaustive enumeration of
all `2^23` colourings of the interior of `B_3` (`dec.c`, `results.txt`)
gives

    kappa_H(3) = P(U ∩ L | C) / (P(U | C) P(L | C)) = 0.999969 < 1,

which is an exact computation. The sampled values stay below 1 for all
`n` from 8 to 512 (previous step, and `results.txt` here). So conditioning
on the one-arm event destroys positive association between the two
half-plane events. Any proof must tolerate `kappa_H < 1`, and the data say
`kappa_H` slowly decreases.

**What is left, and why (ii) survives.** By Theorem C, (ii) does not need
(CD_H). It needs only `delta_H < 7/24 - 2 alpha_H`, a loss of up to about
`n^{-0.037}`. The data put `delta_H` near `0.002`. So the strongest
statement this step leaves standing is (3.2) together with the target

    (T)   liminf_n  log rho_n / log n  >  2 alpha_H - 3/16,
          rho_n = P(U_n ∩ L_n) / (P(U_n) P(L_n)),

a polynomial correlation gain for two explicit increasing events. By
Theorem D, (T) needs input specific to critical percolation.

## 6. Measurements and next step

`dec.c` includes `karm.c` of `experiments/fpbs-wedge-k-arm-2026-09-18`.
It checks four things on every configuration: (1) `D'_n(0) = U_n ∩ L_n`;
(2) `A_n(UH) = U_n` and `A_n(LH) = L_n` on `C_n`; (3) the local forcing of
Lemma 2.1; and (4) the flip of Proposition 2.2. It checks (4) by
recolouring and recomputing `I_n`. `run_all.sh` regenerates
`results.txt`.

| n | configs | P(C) | P(U) | P(C∩U) | P(D') | P(D'∩C) | kappa_H | violations |
|---|---|---|---|---|---|---|---|---|
| 3 | all 2^23 | 0.482817 | 0.773861 | 0.480162 | 0.771206 | 0.477507 | 0.999969 | 0 |
| 8 | 20000 | 0.4492 | 0.6781 | 0.4365 | 0.6591 | 0.4255 | 0.9994 | 0 |
| 16 | 20000 | 0.4143 | 0.6192 | 0.3980 | 0.5914 | 0.3815 | 0.9986 | 0 |
| 32 | 20000 | 0.3837 | 0.5674 | 0.3622 | 0.5325 | 0.3400 | 0.9979 | 0 |
| 64 | 5000 | 0.3630 | 0.5248 | 0.3358 | 0.4840 | 0.3104 | 0.9992 | 0 |
| 128 | 1000 | 0.3380 | 0.4960 | 0.3100 | 0.4430 | 0.2800 | 0.9944 | 0 |

The ratios `P(U)/P(C∩U)` and `P(D')/P(D'∩C)` stay between 1.58 and 1.62,
below the bound 2 of Proposition 2.2. The sampled `kappa_H` values have
statistical errors of about `10^-3` to `10^-2`. The precise drift
`0.9993 -> 0.9923(15)` over `n = 8..512` is the previous step's
large-sample run. With `alpha_H = 0.127` and `zeta(0) = 0.145(4)` from
there, (3.2) gives `delta_H = zeta(0) - 2 alpha_H + 5/48`, which is about
`-0.005 ± 0.006`. That is consistent with the direct `delta_H ≈ 0.002`, and
far below the (ii) threshold `0.037`. CONJECTURE (NUMERICAL):
`alpha_H = 1/8`, `delta_H = 0`, `zeta(0) = 7/48`.

**Next step.** Prove (T), or equivalently
`P(D'_n(0)) >= n^{-3/16 + eps}` for the single increasing event
`D'_n(0) = U_n ∩ L_n`. By (2.1) the one-arm event plays no role. Two
concrete lines:

* *Continuum.* `D'_n(0)` says that in the flipped triangulation `Γ_n` no
  white path joins the two halves of the slit. Identify the scaling limit
  of the white `Γ_n` clusters: white clusters of the CLE6 gasket, with
  touchings through pinch points removed. Then compute the slit-separation
  exponent by an SLE6 martingale. The prediction is `7/48`.
* *Lattice.* Prove a quantitative sharing lemma for the upper and lower
  arms. At a positive fraction `theta` of dyadic scales, conditionally on
  `U_n ∩ L_n` outside the scale, the one-arm crossing of that annulus is
  paid jointly with probability at least `q`. Then compare with Theorem D
  to extract a gain `rho_n >= n^{g(theta, q)}`, which needs `g > 0.067`.
