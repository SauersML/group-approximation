---
rg: 2
id: klingen-rational-twisted-fibres-fail-llp-proof
kind: route
title: The twist dies on qZ^2 x| SL_2(Z), and the bimodular group expectation descends to the fibre
target: klingen-rational-twisted-fibres-fail-llp
requires: []
artifacts:
  - research/artifacts/klingen-central-quotient-2026-09-16.md
---

Full proof: `research/artifacts/klingen-central-quotient-2026-09-16.md`, §1
((1.1): the fibre `A_t` is `C^*(E)` modulo `u_z = e^{2 pi i t}`) and §4
(Theorem 2, Steps 1–4).

1. **Twist dies.**
   - Take `t = p/q`.  `Lambda_q = qZ^2 x| SL_2(Z)` is a subgroup, isomorphic to
     `Lambda` via `(v,g) -> (qv, g)`.
   - On it, `c((qv,g),(qw,h)) = q^2 omega(v, g w)`, so
     `exp(2 pi i t c) = exp(2 pi i pq omega) = 1`.

2. **Expectation descends.**
   - `E_q := preimage of Lambda_q` contains `z`.
   - The group expectation `Phi(u_gamma) = 1_{E_q}(gamma) u_gamma` is ucp and
     `C^*(E_q)`-bimodular (ISW Remark `hereditary`, line 327, citing
     [Pi20, Proposition 3.5]; the bimodularity check is on group elements).
   - `u_z - zeta` lies in `C^*(E_q)` and is central, so
     `Phi((u_z - zeta) x) = (u_z - zeta) Phi(x)`.
   - Hence `Phi(I^E) <= I^{E_q}`, while `I^{E_q} <= I^E`.
   - The induced maps satisfy `Phi- o iota- = id`, where `Phi-` is ucp because
     positive matrices over a quotient lift.  So
     `C^*(E_q)/I^{E_q} -> A_t` is injective with a ucp conditional expectation.

3. **Identify.**
   - `C^*(E_q)/I^{E_q}` is universal for representations `V` of `E_q` with
     `V(z) = zeta`.
   - `x -> V(0,x)` is then a genuine representation of `Lambda_q`, because
     `zeta^{c(x,y)} = 1` by step 1.
   - So the quotient is `C^*(Lambda_q)`, which is isomorphic to `C^*(Lambda)`.

4. **Conclude.**  `C^*(Lambda)` fails the LLP (ISW Corollary B, line 243).  The
   LLP passes to ranges of ucp conditional expectations: finite-dimensional
   operator systems of the range are operator systems of `A_t`, and a ucp map
   `phi` on the range extends to `phi o E`.  So `A_t` fails the LLP.
