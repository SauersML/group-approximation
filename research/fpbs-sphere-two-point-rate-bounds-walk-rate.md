---
rg: 2
id: fpbs-sphere-two-point-rate-bounds-walk-rate
kind: claim
title: The walk connectivity rate is at most rho times cosh of the sphere two-point growth rate
distinct_from:
  fpbs-green-visit-kernel-ordering: that orders pivotal budgets, the l2 gap and non-concentration below finite Green visits; this bounds the walk rate lambda(p) by a purely extrinsic sphere quantity, giving a kernel (G) that needs no pivotal or l2 input.
  fpbs-all-parameter-finite-cluster-spectrum: that bounds the finite-cluster part of a_n by rho^n; this bounds the whole of a_n through the sphere masses E|K_o ∩ S_r|.
artifacts:
  - research/artifacts/fpbs/docs/gauge-certificates-and-sphere-rate-2026-09-17.md
---

**ESTABLISHED (written deduction, Sections 3–4 of the artifact).**

Let `G` be a nonamenable Cayley graph with `rho = ||P||`, and set:

- `M_r(p) = E_p|K_o ∩ S_r|`;
- `g(p) = limsup_r (1/r) log M_r(p)`;
- `lambda(p) = lim_n P_p(o <-> X_n)^(1/n)`.

**Claim.**

1. `rho <= lambda(p) <= rho cosh(max(g(p),0))` for every `p`. The proof is a
   self-contained Chebyshev–Carne bound `p^n(o,x) <= rho^n P(|S_n| >= |x|)`
   followed by Markov's inequality.
2. **(G ⇒ gap)** If some `p > p_c` has `g(p) < arccosh(1/rho)`, then
   `lambda(p) < 1` and `p_c < p <= p_u`.
3. **(EG ⇒ IS)** If `g(p) -> 0` as `p` decreases to `p_c`, then
   `lambda(p) -> rho`, which is (IS) by `fpbs-integrated-pivotal-rate-identity`.
4. `g(p) >= 0` for `p >= p_c`.

**Calibration.** On `T_d` the bound is exact at `p_c`. There
`g(p) = log((d-1)p)` and `arccosh(1/rho) = log sqrt(d-1)`, so (G) holds exactly
for `p < 1/sqrt(d-1)`, the radial l2 range. (G) is therefore strictly stronger
than `lambda(p) < 1` there. The target of (G) is a decaying tilt, which
`fpbs-simon-lieb-gauge-certificates-die-at-pc` shows no Simon–Lieb l1
certificate can supply.
