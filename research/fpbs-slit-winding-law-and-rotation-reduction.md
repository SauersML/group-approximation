---
rg: 2
id: fpbs-slit-winding-law-and-rotation-reduction
kind: claim
title: The FPBS half-plane slit events are exact winding conditions — on the local event E0, U_n fails iff some pinch-free white component's lifted argument range about z0 = (1/2,0) contains an interval [2k pi,(2k+1) pi], and D'_n(0) fails iff it contains some [k pi,(k+1) pi]; hence W_pi ⊆ D'_n(0) ⊆ W_2pi for the rotation-invariant events W_t = {every range is shorter than t}, and after averaging over rotations of the slit, Cauchy-Schwarz credits the one-arm exponent for free, so the rotated (ii) reduces to kappa_n = P(U^Phi ∩ U^{Phi+pi}) / P(U^Phi ∩ U^Psi) >= n^{-delta} with 2 alpha + delta < 7/24; a single wide component always anticorrelates the two sides, and the rotation-invariant proxy W_pi is too lossy to give (ii)
distinct_from:
  fpbs-cd-h-exact-decomposition-and-renewal-obstruction: that splits D'_n(0) = U_n ∩ L_n and shows soft tools cannot produce the correlation gain; this gives an exact geometric formula for U_n, L_n and D'_n(0) as conditions on one real interval per white component, adds a continuous family of rotated slit events that share those intervals, proves the one-arm credit by Cauchy-Schwarz over rotations rather than by conditioning, and isolates the remaining gap as a comparison between antipodal and independent slit directions
artifacts:
  - research/fpbs-slit-winding-law-and-rotation-reduction-proof.md
  - experiments/fpbs-slit-winding-2026-09-19/wind.c
  - experiments/fpbs-slit-winding-2026-09-19/run_all.sh
  - experiments/fpbs-slit-winding-2026-09-19/results.txt
---

**Status.** Theorem A (the winding law), Corollary A' (the sandwich) and
Theorem B (the rotation reduction) are ESTABLISHED. Full proofs are in
`fpbs-slit-winding-law-and-rotation-reduction-proof`. Theorem A is also
checked by sampling for `4 <= n <= 256`, with zero violations. The step
asked of this lane is still OPEN: `P(D'_n(0)) >= n^{-3/16+ε}` from an SLE6
slit-separation exponent, or from a per-scale arm-sharing lemma. What
remains of it is two explicit statements: (K), the comparison
`κ_n >= n^{-δ}`, and (T), a transfer from the rotation average back to the
axis. The route through the rotation-invariant proxy `W_π` is DEAD
numerically. The exponents are NUMERICAL.

**Setting.** As in `fpbs-cd-h-exact-decomposition-and-renewal-obstruction`:

* triangular site percolation at `p = 1/2` in the wired box `B_n`, with
  boundary cluster `I_n`;
* white means "not in `I_n`", and white paths use no pinch step;
* `U_n` and `L_n` are the upper and lower half-plane events, and
  `D'_n(0) = U_n ∩ L_n`.

Let `z0 = (1/2,0)`, the midpoint of the step `e0 = (0,0)(1,0)`, and let
`E0 = {(0,0) ∈ I} ∪ {(1,0) ∈ I} ∪ {(0,1),(1,-1) ∈ I}`. This is the event
that `e0` is not a usable white step. It contains `U_n ∪ L_n` and has
probability `n^{-5/48+o(1)}`.

**Lemma (no winding).** On `E0`, no closed white path winds around `z0`.
So each pinch-free white component `W` carries a lifted argument about
`z0`, and a range `J_W = [m_W, M_W] ⊂ R`, well defined up to a shift in
`2πZ`.

**Theorem A (winding law).** On every configuration,

    U_n     = E0 ∩ {no W with J_W ⊇ [2kπ, (2k+1)π] for some k},
    L_n     = E0 ∩ {no W with J_W ⊇ [(2k-1)π, 2kπ] for some k},
    D'_n(0) = E0 ∩ {no W with J_W ⊇ [kπ, (k+1)π] for some k}.

The whole event is therefore a statement about one real interval per
white component, measured against the grid `πZ` fixed by the axis.

**Corollary A' (sandwich).** Let `W_t = E0 ∩ {|J_W| < t for all W}`. Then
`W_π ⊆ D'_n(0) ⊆ W_{2π}` and `W_π ⊆ U_n ⊆ W_{3π}`. The events `W_t` do
not see the axis. Their scaling limits are rotation-invariant events about
a point of the CLE6 gasket, which makes them the natural targets of a
radial SLE6 computation.

**Theorem B (rotation reduction).** Shift the grid by an angle `φ` to get
the rotated slit events `U^φ` and `L^φ = U^{φ+π}`, with `U^0 = U_n` and
`L^0 = L_n`. Average over independent uniform angles `Φ` and `Ψ`:

* `ū_n = P(U^Φ)`;
* `d̄_n = P(U^Φ ∩ U^{Φ+π})`;
* `κ_n = d̄_n / P(U^Φ ∩ U^Ψ)`.

Then

    d̄_n >= κ_n ū_n^2 / P(E0) >= κ_n ū_n^2 n^{5/48 - o(1)}.

So if `ū_n = n^{-ᾱ}` and `κ_n >= n^{-δ̄}`, the rotation-averaged form of
(ii), `d̄_n >= n^{-3/16+ε}`, holds whenever `2ᾱ + δ̄ < 7/24`.

The Cauchy-Schwarz step gives the one-arm credit `n^{5/48}` for free. All
that is left of "the upper and lower arms pay jointly" is that antipodal
slit directions should be, up to `n^{o(1)}`, as compatible as independent
directions. Pointwise, `g_UL <= g_U^2` iff `|B ∩ (B+π)| <= |B|^2/2π`,
where `B` is the set of bad rotation angles. A single component with
`|J_W| ∈ [π,2π)` gives two disjoint antipodal bad arcs, and so it always
anticorrelates the two sides. That is a plausible source of the small
positive `δ_H`.

**Numerics (NUMERICAL).** Proof, Section 5. The local exponents are over
`8 <= n <= 128`.

* `P(E0)` has exponent about 0.10, matching 5/48.
* `ū_n` has `ᾱ ≈ 0.12`, and `d̄_n` has exponent about 0.14.
* `P(D'_n(0))` has exponent about 0.15. `P(D'_n(0))/d̄_n` settles at
  about 0.97.
* `κ_n` falls from 0.9986 to 0.9766, with `δ̄ ≈ 0.007`. Hence
  `2ᾱ + δ̄ ≈ 0.25 < 7/24 ≈ 0.29`.
* `P(W_π)` has exponent about 0.23, above 3/16. This is why the
  rotation-invariant proxy is dead.
* `W_{3π} = E0` in every sample, and `P(W_{2π})/P(E0) >= 0.987` for
  `n <= 128` (about 0.98 at `n = 256`).

**Dead route.** A radial SLE6 computation of any rotation-invariant
event `W_t` with `t <= π` cannot give (ii). By Corollary A', the largest
`W_t` inside `D'_n(0)` is `W_π`. Numerically its exponent is about
0.23 > 3/16. An SLE route (a) must keep track of the angular
positions of the wide components, the ones with `|J_W| ∈ [π, 2π)`,
against the axis grid.

**Next step.** (ii) follows from two statements.

* **(K)** `κ_n >= n^{-δ}` with `δ < 7/24 - 2ᾱ`. This compares antipodal
  and independent rotations of the slit on one configuration, and needs
  no conditioning on `C_n`. It amounts to near-independent angular
  placement of the wide components across scales.
* **(T)** `P(D'_n(0)) >= n^{-o(1)} d̄_n`, the transfer from the rotation
  average back to the axis slit.

Both are OPEN.
