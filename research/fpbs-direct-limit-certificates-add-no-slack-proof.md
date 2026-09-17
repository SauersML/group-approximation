---
rg: 2
id: fpbs-direct-limit-certificates-add-no-slack-proof
kind: route
title: Covering coupling, Kesten monotonicity with the faithful trace, and ball-locality of DT measures
target: fpbs-direct-limit-certificates-add-no-slack
requires:
  - fpbs-l2-gap-class-closed-under-local-limits
  - fpbs-spectral-dt-certificate-bounds-connectivity-operator
  - fpbs-hp-relative-burton-keane
---

Full proofs are in `research/artifacts/fpbs-direct-limit-certificates-2026-09-17.md`.

1. **Injectivity radius (Lemma 1.1).** A finite ball of `H_0` meets only
   finitely many kernel elements, and each dies at a finite stage. So balls
   eventually map isomorphically, and the maps become graph coverings.
2. **Part 1 (Proposition 2.2).**
   * An adaptive exploration coupling lifts a spanning tree of `K^Gamma(o)` into
     `H_i`, so `p_c(H_i) <= p_c(H_{i+1}) <= p_c(Gamma)`.
   * `fpbs-l2-gap-class-closed-under-local-limits`, Lemma 1.1 of its artifact,
     gives `liminf p_c(H_i) >= p_c(Gamma)`.
3. **Part 2 (Lemmas 3.1–3.2, Proposition 3.3).**
   * `||lambda(a)|| = sup_m a^{*m}(e)^{1/m}` for positive `a = h* * h`, by the
     faithful trace. Pushforward only increases the return terms, which gives
     Kesten monotonicity.
   * For `i >= i(mR)`, the `m`-th return term on `H_i` equals that on `Gamma`,
     which gives convergence.
4. **Part 3 (Lemma 4.1, Theorem 4.2).**
   * DT measures depend only on `B_{r+1}`.
   * Gelfand's formula gives one `n` with `||lambda_Gamma(nu^{*n})|| < 1`,
     which restricts to every approximant.
   * Conversely the monotone limit of approximant norms is the norm on `Gamma`.
5. **Part 4 (Proposition 5.3).**
   * `fpbs-hp-relative-burton-keane` with `H = Gamma` gives `p_c = p_u` on the
     amenable limit.
   * A uniform certificate at `p >= p_c` would give `p < p_sDT <= p_(2->2) <= p_u`
     by `fpbs-spectral-dt-certificate-bounds-connectivity-operator`.
   * The transplant criterion of `fpbs-l2-gap-class-closed-under-local-limits`
     excludes `U_(M,delta)` membership infinitely often.
