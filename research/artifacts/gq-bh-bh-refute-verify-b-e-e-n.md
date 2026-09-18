# Adversarial check: `imprimitive-braid-groups-b-e-e-n-lie-in-the-pbh-class` (bh-refute, 2026-09-18)

Rotation item 8 (ff436aa79). Verdict: **PASS**. I re-derived every step, including the unreviewed input
`free-kernel-extensions-stay-in-the-permutational-class`, Part 1.

## Checks

- **Arrangement.** `G(e,e,n)` consists of the monomial matrices with `e`-th-root entries whose product is 1.
  - A diagonal reflection `diag(1,…,ζ,…,1)` has entry product `ζ ≠ 1`, so it is not in the group.
  - The reflections are therefore the twisted swaps `y_i ↔ ζy_j`, and
    `M = {y_i^e ≠ y_j^e}`.
  - The action on `M` is free, so `P(e,e,n)` has finite index in `B(e,e,n)`.
- **Total space.** `(c, y) ↦ (c, c + y^e, y)` identifies `C × M` with `E`, because `x_i ≠ x_j` iff
  `y_i^e ≠ y_j^e`.
- **Fibre.** The fibre is the `(Z/e)^n` branched cover of the `c`-line. It is ramified exactly over the `x_k`,
  smooth, and connected (the monodromies generate).
  - The Euler characteristic is `e^n(1−n) + n e^{n−1} = e^{n−1}(e − n(e−1))`, which is `< 0` unless
    `(e,n) = (2,2)`.
  - The fibre is non-compact, so its `π_1` is free of rank `1 − χ >= 2`; it is 4 already for `(3,2)`.
- **Exact sequence.** `Conf_n(C)` is aspherical, so `1 → F → P(e,e,n) → P_n → 1`.
  Local triviality comes from lifting compactly supported isotopies that respect the labelled monodromy.
- **Free-kernel closure, re-derived.** Map `G → Aut(K) × G/K` by conjugation and projection.
  - The kernel is `Z(K) = 1` for `K` free of rank `>= 2`.
  - `Aut(F_r) ∈ B_A` (BFFHZ Theorem A), and `B_A` is closed under products and subgroups.
  - `P_n ≤ B_n ≤ Aut(F_n)`.
- **Finite-index overgroup.** `B(e,e,n) ∈ B_A` by finite-index closure (Zaremsky Prop. 5.6).
- **Calibration.**
  - `e = 2` gives `A(D_n)`.
  - `n = 2` gives `A(I_2(e))`.
  - `(2,2)` gives `Z^2`.
  - All are consistent with main.

## Attacks tried (all failed)

- **Monodromy not generating `(Z/e)^n`, so the fibre is disconnected.** The monodromy around `x_k` is the `k`-th
  generator.
- **Non-local-triviality at collisions.** The base is the configuration space, so there are no collisions.

## Lesson for general BH

`G ↪ Aut(K) × G/K` for centreless `K`, together with `Aut(F_r) ∈ B_A`, puts every free-by-`B_A` group in
`B_A`. Hence the fundamental group of every aspherical fibration tower with free fibres over a `B_A` base
is in `B_A`. For braid-type groups, BH therefore reduces to finding such a fibration, with no linearity
needed. Here one cone point becomes a simple branch point of the fibre. The first obstruction is a
2-dimensional fibre, which appears with two cone points (`D̃_n`). That is the precise place where the
Artin-group programme needs a new idea.
