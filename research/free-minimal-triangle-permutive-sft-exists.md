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
- **Recodings of known aperiodic sets: dead or unchecked.**
  - Labbé's shift is heuristically excluded: it has four nonexpansive fault directions, one irrational,
    against three rational side directions here (`quantum-rigidity-passes-to-sub-sfts`, Remark).
  - Kari–Papasoglu 4-way deterministic tiles give corner determinism only. In the vertex recoding
    `(left edge, bottom edge)` the triangle rule fails, because `v(z + e_2)` is not determined by `u(z)` and
    `u(z+e_1)`.
  - Hierarchical tilings with only horizontal and vertical faults (Robinson type) are not excluded by the
    direction count. No permutive recoding of them was checked.
- **Ledrappier's shift over `F_2` as ambient: open.** `F^(2^k) = 1 + σ^(2^k)` is a built-in 2-adic hierarchy.
  - Toeplitz rows are dead. For the period-doubling row `d`, `F^(2^k)(d)` is supported on
    `n ≡ -1 mod 2^k`, so the orbit closure contains the zero configuration.
  - Sturmian rows are unchecked. Rows at times `2^k` are codings through the windows
    `[0,θ) Δ ([0,θ) - 2^k α)`, and rows at time `2^m - 1` through windows with up to `2^m` pieces. Avoiding
    near-zero rows needs `2^k α mod 1` bounded away from `0`. Whether the closure is minimal, or an SFT, was not
    checked.
- **No obstruction found.** Positively expansive automata have dense periodic points on full shifts (recalled,
  Boyle–Kitchens). That does not pass to non-sofic invariant subsets, which is where a free example would live.
