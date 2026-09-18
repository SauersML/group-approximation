---
rg: 2
id: fpbs-integrated-sensitivity-via-fourier-algebra-two-point
kind: route
title: Fourier-algebra membership of the two-point function at parameters decreasing to p_c pins the walk rate at rho with constant one, which is (IS)
target: fpbs-integrated-sensitivity-universal
requires:
  - fpbs-two-point-fourier-algebra-criterion
  - fpbs-two-point-in-fourier-algebra-near-pc-universal
  - fpbs-integrated-pivotal-rate-identity
artifacts:
  - research/artifacts/fpbs/docs/fourier-algebra-two-point-2026-09-17.md
---

Distinct from `fpbs-integrated-sensitivity-via-lq-two-point`, which consumes
`l^q` summability for every `q > 2` ([Q]). This route consumes Fourier-algebra
membership ([A]), which is incomparable with `l^q` summability, and it gives
the exact rate `rho` rather than `rho^(2/q)`.

**The route** (Theorem 5.2 of the artifact).

1. [A] supplies `p_k` decreasing to `p_c` with `tau_(p_k)` in `A(Gamma)^+`.
2. By `fpbs-two-point-fourier-algebra-criterion` (item 2), `a_n(p_k) <= rho^n`,
   so `lambda(p_k) = rho`.
3. `lambda` is nondecreasing and at least `rho`, so `lambda = rho` on
   `(p_c, p_1]`.
4. The rate identity of `fpbs-integrated-pivotal-rate-identity` then gives (IS).

**Also.** Item 2 at `p_1 > p_c` gives nonuniqueness at `p_1`, so `p_c < p_u`.
This is BS directly, without passing through (IS).

**Load-bearing premise.** Only [A],
`fpbs-two-point-in-fourier-algebra-near-pc-universal`.
