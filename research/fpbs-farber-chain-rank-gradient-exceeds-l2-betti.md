---
rg: 2
id: fpbs-farber-chain-rank-gradient-exceeds-l2-betti
kind: claim
title: Some infinite finitely generated residually finite group has a Farber chain whose rank gradient exceeds its first L2 Betti number
root: true
artifacts:
  - research/artifacts/fpbs/docs/cost-betti-rank-gradient-calibration-2026-09-17.md
distinct_from:
  fpbs-kazhdan-positive-rank-gradient: that is the beta_1=0 Kazhdan case, which refutes Fixed Price through Hutchcroft-Pete cost one; this allows any residually finite group and only refutes the equality C(b)=1+beta_1 and so the cycle-tails route
  fpbs-fixed-price-counterexample-exists: that asks for two free actions of different cost; this asks for a gap between rank gradient and beta_1, which is compatible with Fixed Price at a value above 1+beta_1
---

**OPEN counterexample target.** Find an infinite, finitely generated,
residually finite group Gamma and a Farber chain (Gamma_n) with

    RG(Gamma;(Gamma_n)) > beta_1^(2)(Gamma).

By `fpbs-cycle-tails-force-rank-gradient-equals-l2-betti`, such a pair gives
C(b) > 1 + beta_1^(2) for the Bernoulli action of Gamma. So
`fpbs-bernoulli-cycle-tail-compactness` fails, and every route to
`fpbs-free-action-cost-at-least-bernoulli-cost` through zero excess dies. The
pair would also answer Ershov–Lück Question 1.10 (arXiv:1206.0474v3) in the
negative, provided the chain is normal.

Either of two sufficient certificates will do:

- a normal p-chain with trivial intersection whose mod-p gradient exceeds
  beta_1^(2) (EL, remark after Question 1.11);
- for finitely presented Gamma, a normal chain with trivial intersection along
  which d(tors H_1(Gamma_n;Z)) grows linearly in the index.

No such group or chain is constructed here.

## Attempts

* **Certify the gap by computing finitely many quotients.** This cannot work.
  Along any chain, (d(Gamma_n)-1)/[Gamma:Gamma_n] is non-increasing (Schreier).
  Along p-chains, b_1(Gamma_n;F_p)/[Gamma:Gamma_n] is non-increasing (EL
  Theorem 1.6(1)). The same finite-level numbers bound beta_1^(2) from above,
  since beta_1^(2)(Gamma) <= (d(H)-1)/[Gamma:H]. Finite data give only upper
  bounds on both sides. A certificate needs an asymptotic lower bound on RG or
  on a mod-p gradient, which must come from a theorem such as power
  p-deficiency, and a structural upper bound on beta_1^(2). See Section 5 of
  the artifact.
* **Beat beta_1 with a finite presentation of positive power p-deficiency.**
  This yields only a filter.
  - Write r = u_r^(n_r) and let o_G(r) be the order of u_r in G. Root
    uniqueness in free groups gives nu_p(r) = v_p(n_r).
  - The orbifold bound `first-l2-betti-at-least-negative-orbifold-char` gives
    beta_1^(2) >= |X| - 1 - sum 1/o_G(r).
  - So a presentation whose p-deficiency term exceeds beta_1^(2) must have
    sum (1/o_G(r) - p^(-v_p(n_r))) > 0. Some relator root therefore dies below
    the p-part of its exponent: o_G(r) < p^(v_p(n_r)).
  - Presentations with p^(v_p(n_r)) | o_G(r) for every r are useless for this
    target.
  - Infinite presentations, where the orbifold bound is unavailable, are not
    filtered.

  See Section 6 of the artifact.
* **Look in classes where equality is already known.** These classes are
  excluded:
  - residually finite groups with an infinite amenable normal subgroup, where
    RG = 0 by AN Theorem 3 and beta_1^(2) = 0 by Cheeger-Gromov;
  - more generally, any group whose boundary actions all have cost
    1 + beta_1^(2), for instance groups with fixed price 1 + beta_1^(2).
