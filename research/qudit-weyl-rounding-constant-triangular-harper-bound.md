---
rg: 2
id: qudit-weyl-rounding-constant-triangular-harper-bound
kind: claim
title: The triangular Harper sum Z + X + e^(i pi/d) XZ (+ h.c.) forces the qudit Weyl rounding constant above 2d/(sqrt3 pi) - 1, so it is not d/pi + O(1)
artifacts:
  - experiments/qudit-weyl-rounding-triangular-harper-2026-09-17/README.md
distinct_from:
  qudit-weyl-rounding-sharp-constant: that conjectured c_d = d/pi + O(1) from the square Harper sum Z + X (+ h.c.); this proves c_d >= 2d/(sqrt3 pi) - 1 - o(1) with a three-direction sum and a Gaussian trial state, which refutes that conjecture.
  qudit-weyl-rounding-constant-linear-upper-bound: that is the upper bound c_d <= 2/sin(pi/d) + 3, about 2d/pi; this is a lower bound, about 2d/(sqrt3 pi).
---

**ESTABLISHED (ordinary proof, unreviewed, not Lean-verified; route
`qudit-weyl-rounding-constant-triangular-harper-bound-proof`).** Let `d >= 5` be prime and `c_d` the
additive rounding constant of `qudit-weyl-rounding-sharp-constant`. In other words, `c_d` is the least `c`
such that every explicit Weyl sum `K = sum_j c_j g_j` of weight `W`, on any number of qudits, has a
stabilizer state with `<phi|K|phi> >= lambda_max(K) - c (W - lambda_max(K))`. Then

```text
c_d  >=  4 / (2 sqrt3 pi/d + 49 e^(2-d))  -  1   =   2d/(sqrt3 pi) - 1 - O(d^2 e^(-d)).
```

So `c_d - d/pi >= (2/sqrt3 - 1) d/pi - 1 - o(1) = 0.049 d - 1 - o(1)`, which is unbounded. The
conjecture `c_d = d/pi + O(1)` is false. The leading coefficient of `c_d` now lies in
`[2/(sqrt3 pi), 2/pi] = [0.3676, 0.6366]`. The upper end comes from
`qudit-weyl-rounding-constant-linear-upper-bound`.

**The instance.** On one qudit, with `omega = e^(2 pi i/d)`, `Z|x> = omega^x |x>` and `X|x> = |x+1>`,

```text
K = Z + Z^* + X + X^* + T + T^*,      T = e^(i pi/d) X Z = -D(1,1),      W = 6,
```

where `D(a,b) = omega^(2^(-1) a b) X^a Z^b`. The three terms lie on the three distinct lines
`(0,1)`, `(1,0)`, `(1,1)` of `F_d^2`. A one-qudit stabilizer state has zero expectation on every
Weyl operator off its own line, so the best stabilizer value is `2`, and
`F_stab = W - 2 = 4`. The sign on `D(1,1)` matters. `e^(i pi/d) XZ` is the exponential of the
single quadrature `Q - P`, by the Baker–Campbell–Hausdorff phase `e^(i hbar/2)` with `hbar = 2pi/d`.
The finite-field Weyl operator `D(1,1)` differs from it by `-1`, because `2^(-1) = (d+1)/2` mod `d`.
The frustrated choice `+D(1,1)` gives only `c ~ 0.2`.

**Proof idea.** Semiclassically `F = W - K` is the quadratic form `Q^2 + P^2 + (Q-P)^2` with
`[Q,P] = i hbar`. Its ground energy is `hbar sqrt(det) = sqrt3 hbar = 2 sqrt3 pi/d`, where the
square Harper sum has `2pi/d`. The rigorous step evaluates the chirped Gaussian
`psi(x) = exp(-pi(a - ib) x^2/d)`, taken on representatives `|x| <= (d-1)/2`, by Poisson summation.
The three expectations are `exp(-pi/(2ad))`, `exp(-pi(a^2+b^2)/(2ad))` and
`exp(-pi(a^2+(1-b)^2)/(2ad))`, up to exponentially small errors. The choice `a = sqrt3/2`, `b = 1/2`
gives `F(psi) <= 2 sqrt3 pi/d + 49 e^(2-d)`.

**Why this is the natural extremal (heuristic).** In the small-angle regime a Weyl sum with
directions `v_j` and weights `w_j` has `F_min ~ hbar ||D Omega D||_1/2`. Here `Omega` is the integer
symplectic Gram matrix of the directions, `D = diag(sqrt w_j)`, and the rounding gives
`F_stab <= 2(W - m_iso)` from a maximum-weight commuting clique. So `c ~ (d/2pi) rho` with
`rho = 4(W - m_iso)/||D Omega D||_1`.
- For one qudit, `||D Omega D||_1 = 2 sqrt(S)` with `S = sum_(j<k) w_j w_k det(v_j,v_k)^2`.
- The Farey graph (`|det| = 1`) is `K_4`-free. By Motzkin–Straus, `S >= max((W^2 - sum w^2)/2, W^2 - 2 sum w^2)`,
  and this gives `rho <= 4/sqrt3`.
- Equality holds exactly for the triangle.
- Two searches find nothing better than the triangle:
  - over all `{-1,0,1}` Gram matrices with up to 4 directions (multi-qudit included), nothing
    above `4/sqrt3`;
  - exact diagonalization of random weightings of six one-qudit directions at `d = 13, 31`,
    nothing above the triangle.

This is not a proof. It suggests `c_d = 2d/(sqrt3 pi) + O(1)`, but the dual-LP values at `d = 5, 7`
(`1.384`, `2.048`) sit above the triangle (`1.196`, `1.921`), so the `O(1)` term is not settled.

**Numerics** (`experiments/qudit-weyl-rounding-triangular-harper-2026-09-17/`, exact
diagonalization, not used in the proof):

| `d` | 5 | 7 | 11 | 13 | 31 | 61 | 101 | 211 | 401 |
|---|---|---|---|---|---|---|---|---|---|
| triangle `c(K) = 4/F_min - 1` | 1.1958 | 1.9210 | 3.3856 | 4.1193 | 10.7307 | 21.7557 | 36.4571 | 76.8874 | 146.7222 |
| `2d/(sqrt3 pi) - 1` | 0.8378 | 1.5729 | 3.0431 | 3.7782 | 10.3941 | 21.4207 | 36.1228 | 76.5536 | 146.3886 |
| square Harper | 0.935 | 1.510 | 2.765 | 3.399 | 9.12 | 18.67 | 31.40 | 66.41 | |
| `d/pi` | 1.5915 | 2.2282 | 3.5014 | 4.1380 | 9.8676 | 19.4169 | 32.1493 | 67.1634 | 127.6423 |

The triangle beats the square Harper sum for every `d >= 5`, and exceeds `d/pi` from `d = 31` on.
The Gaussian trial state is almost exactly optimal. `F(psi) - F_min` is `4e-4` at `d = 5` and below
`1e-8` from `d = 61` on. The excess `c(K) - (2d/(sqrt3 pi) - 1)` tends to about `1/3`
(`0.3336` at `d = 401`).
