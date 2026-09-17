---
rg: 2
id: qudit-weyl-rounding-constant-linear-upper-bound
kind: claim
title: The additive stabilizer rounding constant for prime-qudit Weyl sums is at most 2/sin(pi/d)+3, which is linear in d
artifacts:
  - experiments/qudit-stabilizer-rounding-constant-2026-09-17/README.md
distinct_from:
  qudit-stabilizer-rounding-for-code-constraint-hamiltonians: that proves SR_d with the quadratic constant 8/sin^2(pi/d)-1 from a triangle-inequality pair bound; this replaces the pair bound by a commutator estimate, sigma_d = sin(pi/d)/(1+2sin(pi/d)), and gets the linear constant 2/sin(pi/d)+3.
---

**ESTABLISHED (ordinary proof, unreviewed, not Lean-verified; route
`qudit-weyl-rounding-constant-linear-upper-bound-proof`).** Let `d` be prime and
`K = sum_j c_j g_j` an explicit Weyl decomposition of a Hermitian operator on `n`
qudits, with weight `W = sum_j |c_j|`. Then some stabilizer state `phi` has

```text
<phi|K|phi>  >=  lambda_max(K) - C_d (W - lambda_max(K)),      C_d = 2/sin(pi/d) + 3.
```

The values are `C_3 = 5.31`, `C_5 = 6.40`, `C_7 = 7.61`, and `C_d ~ 2d/pi`. The earlier
constant was `8/sin^2(pi/d) - 1`, which gives `9.67`, `22.2`, `40.0` and grows like `0.81 d^2`.

**Pair bound.** Let `u, v` be unitaries with `uv = omega^t vu`, `t != 0 mod d`, and
`delta_u = 1 - Re<psi|u|psi>`, `delta_v = 1 - Re<psi|v|psi>`. Then
`delta_u + delta_v >= sigma_d = sin(pi/d)/(1 + 2 sin(pi/d))`. The proof compares two
estimates of `<[u,v]>`: it is at most `4 sqrt(delta_u delta_v)` in modulus, and it
equals `(1 - omega^(-t)) <uv>` with `|<uv>| >= 1 - (sqrt delta_u + sqrt delta_v)^2`.

**Idea.** This is the averaging proof of `qudit-stabilizer-rounding-for-code-constraint-hamiltonians`.
Terms with `delta < sigma_d/2` commute, so fix a joint eigenvalue pattern on them and
average over the stabilizer states of that joint eigenspace. Every undetermined term
averages to zero. The only change is the threshold `tau = sigma_d/2` instead of
`sin^2(pi/d)/8`.

**Not sharp.** Numerically, lower bounds on the best constant grow like `d/pi` (Harper sum
`Z + Z^* + X + X^*`). So the best constant is expected to be `Theta(d)`, with leading
coefficient between `1/pi` and `2/pi`; see `qudit-weyl-rounding-sharp-constant`. For code-constraint
Hamiltonians the multiplicative factor is bounded and sharp:
`qudit-code-rounding-factor-one-plus-inv-sqrt-d`.

**Consequence.** For explicit prime-`d` Weyl sums, deciding `lambda_max(K) >= a`
versus `lambda_max(K) <= b` is in NP when `b < a - C_d (W - a)`. The witness is a
stabilizer tableau. The frustration `W - a` that can be tolerated is now about
`(a - b) sin(pi/d)/2`, where it was about `(a - b) sin^2(pi/d)/8`.
