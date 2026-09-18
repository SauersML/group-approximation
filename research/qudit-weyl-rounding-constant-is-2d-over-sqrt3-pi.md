---
rg: 2
id: qudit-weyl-rounding-constant-is-2d-over-sqrt3-pi
kind: claim
title: The qudit Weyl stabilizer rounding constant on any number of prime-d qudits is 2d/(sqrt3 pi) + O(1)
root: true
artifacts:
  - experiments/qudit-weyl-rounding-multiqudit-2026-09-18/README.md
distinct_from:
  qudit-weyl-rounding-sharp-constant: that conjectured d/pi + O(1), which the triangular Harper sum refutes; this is the replacement conjecture with leading coefficient 2/(sqrt3 pi).
  qudit-weyl-rounding-one-qudit-constant-is-2d-over-sqrt3-pi: that proves the same asymptotics on one qudit; this asks for it on any number of qudits.
---

**OPEN (the lower half is proved; the upper half is reduced to a matrix inequality).** Let `d >= 5`
be prime. Let `c_d` be the constant of `qudit-weyl-rounding-sharp-constant`: the least `c` such that
every Weyl sum `K = sum_j c_j g_j` on any number of qudits, with weight `W`, has a stabilizer state
with `<phi|K|phi> >= lambda_max - c (W - lambda_max)`. The conjecture is

```text
c_d = 2d/(sqrt3 pi) + O(1).
```

**Status of the two halves.**
- `c_d >= 2d/(sqrt3 pi) - 1 - o(1)`: proved (`qudit-weyl-rounding-constant-triangular-harper-bound`).
- `c_d <= 2d/(sqrt3 pi) + 4 + O(1/d)` on **one** qudit: proved
  (`qudit-weyl-rounding-one-qudit-constant-is-2d-over-sqrt3-pi`).
- On any number of qudits, the same upper bound `c*(d) <= 2d/(sqrt3 pi) + 4 + 1.21/d` follows from the
  Hermitian trace-norm inequality `hermitian-edge-trace-norm-vs-independence`. This is route
  `qudit-weyl-rounding-constant-2d-over-sqrt3-pi-via-trace-norm`, which proves that direction only.
  The best unconditional upper bound for `n >= 2` is still `2/sin(pi/d) + 3`, about `2d/pi`.

**Evidence that `n >= 2` gives nothing larger.** All integer symplectic Gram matrices occur on
enough qudits. The semiclassical figure of merit `rho = 4(W - m_iso)/||D Omega D||_1` (see
Attempt 3 of `qudit-weyl-rounding-sharp-constant`) was searched with `rho_search.py`. Random
integer antisymmetric `Omega` with `N <= 7` directions and entries in `{-2, ..., 2}`, with weights
optimized, never exceeded the one-qudit triangle value `4/sqrt3 = 2.3094`. Several `{-1,0,1}`
searches hit `4/sqrt3` exactly, including a flat face with non-triangle weights.

## Attempts

1. *Multi-qudit symplectic Gram beats the one-qudit triangle* (w5-078, the heretic direction).
   Refutation would need an `n`-qudit configuration with `rho > 4/sqrt3`. It dies numerically in the
   semiclassical class: `rho_search.py`, `graph_relaxed.py` and `complex_star.py` find `4/sqrt3`
   (equivalently the ratio `sqrt3`) as the minimum everywhere, always at a triangle. The class not
   searched is non-semiclassical states with `delta_j` of order `1`. There (L3) of Lemma L is weak.
   But the one-qudit proof shows that such terms cost the `+O(1)` only.
2. *Commutator-Gram trace norm plus commuting-set rounding*
   (`qudit-weyl-rounding-constant-2d-over-sqrt3-pi-via-trace-norm`). It reduces the upper bound to
   (**), and dies only at (**) for graphs with non-clique STAB facets or large cliques.
