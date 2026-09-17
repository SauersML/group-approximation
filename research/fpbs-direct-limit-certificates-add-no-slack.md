---
rg: 2
id: fpbs-direct-limit-certificates-add-no-slack
kind: claim
title: On a direct limit of marked groups, a spectral DT certificate exists iff one finite certificate holds uniformly on the approximants, so per-approximant gaps never transfer
distinct_from:
  fpbs-l2-gap-class-closed-under-local-limits: that shows a uniform operator gap (M, delta) passes to arbitrary local limits and that finite or amenable approximants never supply one; this treats surjective chains of infinite groups, proves the converse direction (the limit certificate restricts to every approximant with the same data), proves p_c increases to the limit so the margin is free, and shows that hyperbolic approximants with strict gaps can converge to an amenable limit.
  fpbs-spectral-dt-certificate-bounds-connectivity-operator: that proves a certificate on one graph bounds T_p; this compares certificates across a chain of covers and proves they are monotone and converge in norm.
  fpbs-quotient-spectral-dt-certificates-are-subgroup-blind: that compares a group with its Schreier quotients by subgroups; this compares a group with the covering groups of a direct-limit presentation, where the kernel grows with i.
  free-burnside-is-a-limit-of-hyperbolic-groups: that is the literature presentation of B(m,N) as a limit of hyperbolic groups; this says what percolation information that presentation can carry to the limit.
artifacts:
  - research/artifacts/fpbs-direct-limit-certificates-2026-09-17.md
---

**ESTABLISHED.** Let `(H_i, D)` be a surjective chain of marked groups with
direct limit `Gamma`. That means label-preserving surjections
`H_i -> H_{i+1} -> Gamma` whose kernels exhaust `ker(H_0 -> Gamma)`. Let
`nu_{S,p}` be the DT boundary measure of
`fpbs-spectral-dt-certificate-bounds-connectivity-operator`, pulled back to
`H_i` through the eventual ball isomorphism.

1. **Thresholds.** `p_c(H_i)` is nondecreasing and converges to `p_c(Gamma)`.
   The proof uses a covering coupling and DT lower semicontinuity.
2. **Monotone norms.** For every finitely supported `f >= 0` on `Gamma`,
   `||lambda_{H_i}(f_i)||` is nondecreasing in `i` and converges to
   `||lambda_Gamma(f)||`. Also `sp_{H_i}(nu_i)` is nondecreasing and at most
   `sp_Gamma(nu)`.
3. **No slack.** `sp_Gamma(nu_{S,p}) < 1` iff there are `n` and `c < 1` with
   `||lambda_{H_i}(nu_{S,p}^{*n})|| <= c` for infinitely many `i`, equivalently
   for all large `i`.
   * So `p_c(Gamma) < p_sDT(Gamma)` iff one finite datum `(S, p, n, c)` with
     `p > p_c(Gamma)` certifies infinitely many approximants.
   * A certificate on `Gamma` is a certificate on every approximant.
4. **Abstract calibration.** If `Gamma` is amenable, then for every
   `(S, p >= p_c(Gamma), n, c < 1)` only finitely many `i` are certified. Also,
   for all `(M, delta)`, only finitely many `H_i` lie in `U_(M,delta)`. This
   holds whatever gaps the `H_i` carry.

**Obstruction (killed class).** Consider derivations of `p_c < p_u` on a
direct limit of hyperbolic groups, such as `B(m,N)` in any marking, from
per-approximant theorems with `i`-dependent constants. Examples are Hutchcroft's
hyperbolic L2 gap, Choi–Seo, `p_u = 1` on infinitely-ended approximants, and
per-approximant spectral certificates. Every such derivation dies at the
passage `i -> infinity`.

* By Part 3 the only transferable datum is a uniform certificate, which is the
  certificate on `Gamma` itself.
* The margin is never the issue, by Part 1.

**Calibration (recorded, not claimed).** The lamplighter truncations
`H_i = <a,t | a^2, [a, t^{-k} a t^k], k <= i>` are HNN extensions of
`(Z/2)^{i+1}`. They are virtually free, so each has `p_c < p_(2->2)`. They
converge to `Z/2 wr Z`, where `p_c = p_u`. This uses textbook Bass–Serre and
Švarc–Milnor inputs that are not imported.

Proofs: artifact Sections 1 to 4 and Proposition 5.3. Corollary 6.1 records
the Burnside instance. Section 7 records the spark M3, a uniform margin over
subgroups of hyperbolic groups with bounded spectral radius.
