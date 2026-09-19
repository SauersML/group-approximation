---
rg: 2
id: fpbs-slit-winding-law-and-rotation-reduction-proof
kind: route
title: Proof that the half-plane slit events U_n, L_n and D'_n(0) are exactly winding conditions on the lifted argument ranges of the pinch-free white components about the slit point z0 = (1/2,0), of the rotation-invariant sandwich W_pi ⊆ D'_n(0) ⊆ W_2pi, and of the rotation-averaged Cauchy-Schwarz bound that credits the one-arm exponent for free and leaves only the antipodal-versus-independent comparison kappa_n
target: fpbs-slit-winding-law-and-rotation-reduction
requires:
  - fpbs-cd-h-exact-decomposition-and-renewal-obstruction
---

## 0. Setting

Notation is as in `fpbs-cd-h-exact-decomposition-and-renewal-obstruction`
(Section 0 there). Triangular site percolation at `p = 1/2`, axial
coordinates `(i,j)`, embedding `x = i + j/2`, `y = j sqrt(3)/2`, steps
`d_0..d_5 = (1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)`. `B_n` is wired, `I_n`
is the black cluster of `∂B_n`, a site is *white* if it is not in `I_n`,
a step `c -> c+d_k` is a *pinch* if `c+d_{k-1}, c+d_{k+1}` are both in
`I_n`, and a *white path* is a path of white sites with no pinch step.
`S_n = {(i,0): -n < i <= 0}`, `P_n = {(i,0): 1 <= i <= n-1}`. `U_n`, `L_n`
are the half-plane events of that node, and `D'_n(0) = U_n ∩ L_n`
(its Theorem A). White sites are interior sites of `B_n`, because boundary
sites are in `I_n`.

The *slit point* is `z0 = (1/2, 0)`, the midpoint of the step
`e0 = {(0,0),(1,0)}`. The common neighbours of `(0,0)` and `(1,0)` are
`(0,1)` and `(1,-1)`. Let

    E0 = {(0,0) ∈ I_n} ∪ {(1,0) ∈ I_n} ∪ {(0,1),(1,-1) ∈ I_n}.

Equivalently, `E0` is the event that `e0` is not a white step of a white
path. Paths are drawn as polygons made of the unit segments of their
steps. `arg` means the argument about `z0`.

## 1. Geometry of the axis

**Lemma 1.** (a) The only lattice segment containing `z0` is `e0`.
(b) Let `σ` be a lattice segment other than `e0`, and `p ∈ σ` with
`arg(p) ∈ πZ`. Then either `p` is an endpoint of `σ` in row `j = 0`, or
`σ` lies in row `0` and `arg` is constant on `σ`.

*Proof.* A segment joins sites in the same row or in adjacent rows. It
meets the line `y = 0` at a point that is not an endpoint only if it
lies in row 0. Row-0 segments are `[(i,0),(i+1,0)]`, with `x ∈ [i,i+1]`.
This contains `x = 1/2` only for `i = 0`. A row-0 segment other than `e0`
lies in `{x <= 0}` or in `{x >= 1}`, where `arg` is `π` or `0`. □

**Lemma 2.** `U_n ∪ L_n ⊆ E0`.

*Proof.* Off `E0`, both `(0,0)` and `(1,0)` are white and `e0` is not a
pinch. So the one-step path `(0,0) -> (1,0)` is a white path inside
`{j = 0}` from `S_n` to `P_n`. □

## 2. No white circuit winds around z0

**Lemma 3.** On `E0`, every closed white path has winding number 0 about
`z0`.

*Proof.* Let `γ` be a closed white path. On `E0`, `γ` does not use `e0`.
Either an endpoint of `e0` is black, or `e0` is a pinch. By Lemma 1(a),
`z0 ∉ γ`. Choose `b ∈ I_n` as follows: `b = (0,0)` or `b = (1,0)` if that
site is in `I_n`, and otherwise `b = (0,1)`, which is in `I_n` by `E0`.
Let `τ` be the straight segment from `z0` to `b`.

* In the first case, `τ` is half of `e0`.
* In the second case, `τ` is the median of the triangle
  `{(0,0),(1,0),(0,1)}`, and apart from `z0` it lies in the open triangle
  together with its vertex `b`.

Lattice segments meet only at common endpoints and never enter open
triangles. So a segment of `γ` meeting `τ` would have to be `e0`, or pass
through `b`. `γ` does neither, because `b` is black. Hence
`wind(γ, z0) = wind(γ, b)`.

Since `b ∈ I_n`, there is a path `β` of `I_n` sites from `b` to a site
`c ∈ ∂B_n`. Take a neighbour `c'` of `c` outside `B_n`, and then a lattice
path from `c'` to infinity through sites outside `B_n`. That set is
connected: from any such site, a step that increases `|j|` or `|2i+j|`
stays outside. No site of the concatenated path `β'` is a site of `γ`.
Two lattice segments with no common endpoint are disjoint, so `β'` and
`γ` are disjoint as planar sets, and the winding number of `γ` is constant
along `β'`. It is `0` at infinity. So `wind(γ, b) = 0`. □

**Consequence (lifted argument).** Let `W` be a component of the graph of
white sites whose edges are the non-pinch steps, taken on `E0`. Its
polygon avoids `z0`. By Lemma 3, `arg` has a continuous lift `θ_W` on the
union of the segments of `W`. The lift is unique up to adding a constant
in `2πZ`, and it is constructed by breadth-first search, adding the angle
each segment subtends at `z0`. That angle lies in `(-π,π)` by Lemma 1(a).
Along each segment `θ_W` is monotone, so the range

    J_W = [m_W, M_W]

is attained at sites. Its length `|J_W| = M_W - m_W` is independent of
the choice of lift, and so is the family of conditions below.

## 3. Theorem A (winding law)

**Theorem A.** On every configuration,

    U_n     = E0 ∩ {no W and k ∈ Z with [2kπ, (2k+1)π] ⊆ J_W},
    L_n     = E0 ∩ {no W and k ∈ Z with [(2k-1)π, 2kπ] ⊆ J_W},
    D'_n(0) = E0 ∩ {no W and k ∈ Z with [kπ, (k+1)π] ⊆ J_W}.

*Proof.* Start with `U_n`. By Lemma 2 we may work on `E0`.

(⊆) Suppose `[2kπ,(2k+1)π] ⊆ J_W`. Pick sites `v, w ∈ W` with
`θ_W(v) >= (2k+1)π` and `θ_W(w) <= 2kπ`, and a white path `γ` in `W`
from `v` to `w`, parametrised along its segments. Let `t1` be the first
time with `θ = 2kπ`, and `t0 < t1` the last earlier time with
`θ = (2k+1)π`. On `(t0,t1)` the lift stays in the open interval, so `γ`
is in `{y > 0}`. By Lemma 1(b), `γ(t0)` and `γ(t1)` are row-0 sites.
If the lift is constant on a row-0 segment, the extreme times are
attained at its endpoints. `γ(t0)` has `arg = π`, so `x <= 0`, and it is
interior, so `γ(t0) ∈ S_n`. `γ(t1)` has `arg = 0`, so `x >= 1`, and it is
interior, so `γ(t1) ∈ P_n`. Every site strictly between has `j >= 1`.
This sub-path is a white path in `{j >= 0}` from `S_n` to `P_n`, so
`U_n` fails.

(⊇) Suppose `U_n` fails on `E0`. Take a white path `γ` in `{j >= 0}`
from `v0 ∈ S_n` to `vr ∈ P_n`, lying in one component `W`. Its polygon is
in `{y >= 0}` and avoids `z0`: by Lemma 1(a), because `e0` is not a
non-pinch white step on `E0`. There `arg ∈ [0,π]`. The lift is
continuous and takes values in `∪_k [2kπ,(2k+1)π]`, so it stays in one
such interval. `arg(v0) = π` because `x(v0) <= 0 < 1/2`, and
`arg(vr) = 0` because `x(vr) >= 1`. So `θ(v0) = (2k+1)π`,
`θ(vr) = 2kπ`, and `J_W ⊇ [2kπ,(2k+1)π]`.

For `L_n`, the reflection `(x,y) -> (x,-y)` fixes `z0` and `E0`,
exchanges `U_n` and `L_n`, maps components to components, and replaces
`θ` by `-θ`. For `D'_n(0)`, use `D'_n(0) = U_n ∩ L_n`. □

**Corollary A' (rotation-invariant sandwich).** Let `ℓ*` be the maximum of
`|J_W|` over the components on `E0`, and `W_t = E0 ∩ {ℓ* < t}`. Then

    W_π ⊆ D'_n(0) ⊆ W_{2π},   W_π ⊆ U_n ⊆ W_{3π}.

*Proof.* An interval of length `< π` contains no interval of length `π`.
An interval `[m,M]` with `M - m >= 2π` contains `[kπ,(k+1)π]` for the
`k` with `kπ ∈ [m, m+π)`. With `M - m >= 3π` it contains
`[2kπ,(2k+1)π]` for the `k` with `2kπ ∈ [m, m+2π)`. □

`W_t` depends only on the lengths `|J_W|`. So, unlike `U_n` and
`D'_n(0)`, it does not refer to the axis, and its conjectural scaling
limit is a rotation-invariant event about a gasket point.

## 4. Theorem B (rotation reduction)

For `φ ∈ R`, let `U^φ = E0 ∩ {no W, k with [φ+2kπ, φ+(2k+1)π] ⊆ J_W}` and
`L^φ = U^{φ+π}`. These are the rotated slit events: they are defined by
the right-hand side of Theorem A with the grid `πZ` shifted by `φ`, and no
lattice rays are needed. By Theorem A, `U^0 = U_n` and
`L^0 = L_n`. Let

    g_U  = (1/2π) ∫_0^{2π} 1[U^φ] dφ,
    g_UL = (1/2π) ∫_0^{2π} 1[U^φ ∩ U^{φ+π}] dφ,

and `ū_n = E g_U`, `d̄_n = E g_UL`. If `Φ, Ψ` are independent uniform
angles, independent of the configuration, then `ū_n = P(U^Φ)`,
`d̄_n = P(U^Φ ∩ L^Φ)`, and `E[g_U^2] = P(U^Φ ∩ U^Ψ)`. Put

    κ_n = d̄_n / E[g_U^2] = P(U^Φ ∩ U^{Φ+π}) / P(U^Φ ∩ U^Ψ),

which compares antipodal directions with independent ones.

**Theorem B.** `d̄_n >= κ_n ū_n^2 / P(E0)`. Moreover
`P(E0) <= n^{-5/48+o(1)}`. Hence, if `ū_n = n^{-ᾱ+o(1)}` and
`κ_n >= n^{-δ̄+o(1)}`, then

    d̄_n >= n^{-(2ᾱ - 5/48 + δ̄) + o(1)},

and the rotation-averaged form of (ii), `d̄_n >= n^{-3/16+ε}`, holds as
soon as `2ᾱ + δ̄ < 7/24`.

*Proof.* `0 <= g_U <= 1[E0]`, so by Cauchy-Schwarz
`ū_n^2 = E[g_U 1[E0]]^2 <= P(E0) E[g_U^2]`. Then
`d̄_n = κ_n E[g_U^2] >= κ_n ū_n^2 / P(E0)`. `E0` is contained in the union
of the events that one of the sites `(0,0), (1,0), (0,1)` is joined by a
black path to `∂B_n`, at distance `>= n-2`. Each has probability
`n^{-5/48+o(1)}` by the one-arm exponent (Lawler-Schramm-Werner). Finally,
`3/16 = 2ᾱ - 5/48 + δ̄` is the same as `2ᾱ + δ̄ = 7/24`. □

**Remark (why antipodal pairs repel).** Write `B` for the set of bad `φ`
for `U^φ`. Then `g_U = 1 - |B|/2π` and `g_UL = 1 - |B ∪ (B+π)|/2π`, so

    g_UL <= g_U^2  iff  |B ∩ (B+π)| <= |B|^2/2π.

The pointwise bound can fail. For one component with `|J_W| ∈ [π,2π)`,
`B` is an arc of length `|J_W| - π < π`, and `B ∩ (B+π) = ∅`. So a single
wide component always anticorrelates the two sides.

Here is a toy model, not the percolation measure. Give the wide
components fixed lengths, and independent uniform offsets. Put
`x_W = (|J_W| - π)/2π ∈ [0, 1/2)`. Then

    P(U) = P(L) = Π (1 - x_W),    P(U ∩ L) = Π (1 - 2 x_W) <= P(U) P(L).

The defect factor `Π (1 - x_W^2/(1-x_W)^2)` is of second order in the
`x_W`. This is a plausible mechanism for the small but positive `δ_H` of
the previous node, and for `κ_n < 1` in Section 5. It is NUMERICAL and
HEURISTIC.

## 5. Numerics (NUMERICAL, not proved)

`experiments/fpbs-slit-winding-2026-09-19/wind.c` samples the wired box.
For each sample it computes the following:

* `U_n` and `L_n` directly, by half-plane breadth-first search;
* the lifted ranges `J_W` of every pinch-free white component on `E0`;
* the winding-law predictions of `U_n` and `L_n`;
* `W_π`, `W_{2π}` and `W_{3π}`;
* `g_U` and `g_UL`, on 720 angle bins.

Over all samples (`40000` at `n <= 32`, `20000` at `n = 64`, `10000` at
`n = 128`, `1500` at `n = 256`), there are zero violations of Lemma 2,
Lemma 3 and Theorem A. At `n = 8` and `n = 16` the direct values of
`P(U_n)`, `P(C_n)` and `P(D'_n)` agree with `dec.c` of the previous node,
seed for seed.

The local exponents below are `-log2` of the ratio between consecutive
`n`, taken over `8 <= n <= 128`. The results table is in `results.txt`.

| quantity | local exponents | estimate |
|---|---|---|
| `P(E0)` | 0.106, 0.119, 0.093, 0.105, 0.080 | 5/48 ≈ 0.104 |
| `ū_n` | 0.123, 0.141, 0.114, 0.126, 0.102 | `ᾱ ≈ 0.12` |
| `d̄_n` | 0.140, 0.164, 0.136, 0.147, 0.126 | ≈ 0.14 |
| `P(D'_n(0))` | 0.159, 0.168, 0.139, 0.152, 0.127 | ≈ 0.15 |
| `κ_n` | 0.0044, 0.0065, 0.0067, 0.0066, 0.0080 | `δ̄ ≈ 0.007` |
| `P(W_π)/P(E0)` | 0.122, 0.137, 0.134, 0.135, 0.115 | ≈ 0.13 |

What the numbers say:

* **`κ_n`.** It is below 1 at every `n` (0.9986 down to 0.9766), and its
  exponent is tiny. So `2ᾱ + δ̄ ≈ 0.25 < 7/24 ≈ 0.29`, and Theorem B
  would give the rotated (ii) with room to spare.
* **Axis versus rotated.** The ratio `P(D'_n(0))/d̄_n` settles at about
  0.97 (0.994, 0.981, 0.978, 0.976, 0.973, 0.972). So the axis event and
  its rotation average have the same exponent.
* **`W_{2π}` and `W_{3π}`.** For `n <= 128`, `P(W_{2π})/P(E0) >= 0.987` and
  `W_{3π} = E0` in every sample. Components winding more than `2π` about
  `z0` are rare, and all the cost of `D'_n(0)` beyond `E0` comes from
  components with range in `[π, 2π)`.
* **`n = 256` (1500 samples, noisy).** `κ_256 ≈ 0.969`,
  `P(D'_n(0))/d̄_n ≈ 0.988`, `P(W_{2π})/P(E0) ≈ 0.981`, and `W_{3π} = E0`
  in every sample. The step `128 -> 256` has a local exponent standard
  error of about 0.05, so it is left out of the table. Its raw local
  exponents (`ū` 0.15, `κ` 0.011) are consistent with the table within
  that error, but on their own they do not confirm `2ᾱ + δ̄ < 7/24`.
* **The proxy `W_π` is dead.** Its exponent is about
  `5/48 + 0.13 ≈ 0.23 > 3/16`. The rotation-invariant lower bound
  `W_π ⊆ D'_n(0)` therefore cannot give (ii), even if `w(π)` were
  computed exactly by radial SLE6. So route (a) of the previous node's
  next step, done via a rotation-invariant event, is closed. A successful
  route (a) must keep the axis grid, that is, the angular positions of the
  wide components.

## 6. What is left

(ii) now follows from two statements.

1. **(K)** `κ_n >= n^{-δ}` for some `δ < 7/24 - 2ᾱ`. Here `ᾱ` is the
   exponent of `ū_n`, and the bound only needs `ᾱ <= α_H + o(1)`.
2. **(T)** `P(D'_n(0)) >= n^{-o(1)} d̄_n`, the transfer from the rotated
   average back to the axis.

For (K), a single wide component always gives antipodal repulsion
(Section 4, Remark). So (K) says that the wide components at different
scales place their bad arcs nearly independently. That is a statement of
per-scale mixing of angular positions, conditional on `E0`. Unlike the
conditional decorrelation (CD_H) of the previous node, it involves no
conditioning on `C_n`. It compares two rotations of the same
configuration. Whether the product-model obstruction of that node applies
to (K) is OPEN.

For (T), a natural approach is to rotate the grid offset one annulus at a
time, gluing with RSW. It is not a proof, because the offset is global:
every scale sees the same `φ`. So (T) needs a lemma that changing the
offset only at scales `<= r` costs a constant factor. That lemma is OPEN.
Numerically, (T) holds with ratio about 0.97 (Section 5).
