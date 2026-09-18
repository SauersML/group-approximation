---
rg: 2
id: free-minimal-triangle-permutive-sft-exists
kind: claim
title: Some free minimal Z^2 subshift of finite type is triangle-permutive, equivalently some finite quasigroup spacetime contains a free minimal sub-SFT
distinct_from:
  permutive-triangle-sfts-are-quantum-rigid: that proves triangle-permutive SFTs rigid and that periodic rows force periodic points; this asks whether any of them is free and minimal.
  free-minimal-z2-sft-is-quantum-rigid: that asks for rigidity by any mechanism; this is the one mechanism with a reviewed rigidity proof, posed as an existence problem in symbolic dynamics.
---

**OPEN.** There is a free minimal `Z^2`-SFT `Ω` such that, in some recoding, any two of `x(z)`, `x(z+e_1)`,
`x(z+e_2)` determine the third. Here is an equivalent form, via Evans' theorem that a partial Latin square of
order `n` embeds in a Latin square of order `2n` (recalled). For some finite quasigroup `(Q, ⋆)`, the
spacetime `X_⋆ = {x ∈ Q^(Z^2) : x(z+e_2) = x(z) ⋆ x(z+e_1)}` contains a free minimal sub-SFT.

**Payoff.** By `permutive-triangle-sfts-are-quantum-rigid` (reviewed PASS), such an `Ω` is quantum rigid. Its
crossed product over a finite field is then a finitely presented simple algebra with a faithful rank function:
gate (a), with no dependence on the open `wall-rigid-z2-sft-is-quantum-rigid`. By
`quantum-rigidity-passes-to-sub-sfts`, any free minimal sub-SFT of `X_⋆` inherits rigidity.

**Refutation.** A proof that every nonempty sub-SFT of every quasigroup spacetime has a periodic point.

## Attempts

- **Forced structure.**
  - Rows evolve by the bipermutive radius-one-half automaton `F(x)_i = x_i ⋆ x_(i+1)`, columns by a second one,
    and antidiagonals, backwards, by a third.
  - A horizontally periodic row gives a doubly periodic point (predecessor's Proposition 5). So the row
    subshift must be non-sofic without periodic points, and every `F`-cycle of `p`-periodic rows must meet a
    forbidden pattern, for every `p`.
- **Markov criterion (partial obstruction).**
  - The trace `x -> (F^n(x)_0)_(n>=0)` conjugates the right-permutive automaton `F^+` on right half-rows `Y^+`
    to the upward shift on one-sided columns `X_c^+`.
  - A positively expansive open map is conjugate to a one-sided SFT (Parry's theorem, recalled). So if `F^+` is
    open on `Y^+`, then `X_c^+` is an SFT, it has a periodic column, and Proposition 5 gives a periodic point.
    The same holds with rows and columns exchanged.
  - A free example therefore needs both one-sided automata to be non-open on the relevant subshifts. The
    obvious local lift `x'_0 = x_0` of a nearby row need not stay legal far from the corner, so openness is not
    automatic.
- **Complexity constraint (Ledrappier ambient).** Kari–Moutot, arXiv:1806.07107, Theorem 6 (read from the
  source PDF, page 5): "Any low complexity `c ∈ X_(f_L)` is periodic", where low complexity means
  `|P(c, D)| <= |D|` for some finite shape `D`. So a free sub-SFT of Ledrappier's shift has
  `|L_D(Ω)| > |D|` for every shape `D`. Their Section 3 extends this to algebraic subshifts over `F_p` whose
  polynomial has line factors in at most one direction. Their Lemma 7 (page 6): a configuration annihilated by
  two coprime polynomials is two-periodic. So no free example lies inside two coprime algebraic shifts.
- **Recodings of known aperiodic sets: dead or unchecked.**
  - Labbé's shift is heuristically excluded: it has four nonexpansive fault directions, one irrational,
    against three rational side directions here (`quantum-rigidity-passes-to-sub-sfts`, Remark).
  - Kari–Papasoglu 4-way deterministic tiles give corner determinism only. In the vertex recoding
    `(left edge, bottom edge)` the triangle rule fails, because `v(z + e_2)` is not determined by `u(z)` and
    `u(z+e_1)`.
  - Kari's multiplier tiles fail too. The sequential carry makes the tile at `(i+1, n)` a function of the tiles
    at `(i, n)` and `(i+1, n-1)`, but the other two projections of that triangle are not injective.
  - Hierarchical tilings with only horizontal and vertical faults (Robinson type) are not excluded by the
    direction count. No permutive recoding of them was checked.
- **Ledrappier's shift over `F_2` as ambient: open.** `F^(2^k) = 1 + σ^(2^k)`, and `c -> (1+X+Y) c(X^2, Y^2)` is a
  linear inflation preserving `X_L`. Both give a built-in 2-adic hierarchy.
  - Toeplitz rows are dead. For the period-doubling row `d`, `F^(2^k)(d)` is supported on
    `n ≡ -1 mod 2^k`, so the orbit closure contains the zero configuration.
  - Sturmian rows are unchecked. Rows at times `2^k` are codings through the windows
    `[0,θ) Δ ([0,θ) - 2^k α)`, and rows at time `2^m - 1` through windows with up to `2^m` pieces. Avoiding
    near-zero rows needs `2^k α mod 1` bounded away from `0`. Whether the closure is minimal, or an SFT, was not
    checked.
  - Zero-run constraints are too weak. Forbidding long zero runs in all rows forbids long `2^k`-periodic
    stretches of row `0`, but `110`-periodic rows survive, giving periodic points.
- **No obstruction found.** Positively expansive automata have dense periodic points on full shifts (recalled,
  Boyle–Kitchens). That does not pass to non-sofic invariant subsets, which is where a free example would live.
- **Exhaustive small-window search: every case is empty or periodic** (`small-window-quasigroup-sub-sfts-have-periodic-points`,
  sw-109, 2026-09-17).
  - Every sub-SFT with forbidden shapes inside the upward triangle `Δ_L` is `Ω(A)`: all length-`L` row words lie
    in `A`.
  - A complete branch and bound over essential `A` combines the periodic-cycle hypergraph `{W_C}`, level automata
    for `Z_n(A)` and certification of long cycles. It found **zero** aperiodic candidates for Ledrappier with
    `L <= 6`, all 5 order-3 quasigroups with `L <= 3`, and all 35 order-4 quasigroups with `L = 2`. Script and
    logs: `experiments/triangle-permutive-sft-search-2026-09-17/`.
  - So a free example needs windows beyond these, for instance boxes with `w + h >= 8` over `F_2`, or order `>= 5`.
  - Emptiness certificates close within at most 8 levels, and alive leaves always had certifiable periodic rows,
    some of period larger than 16. Both suggest the refutation form (every nonempty sub-SFT has a periodic point)
    is the right conjecture to attack by proof.
