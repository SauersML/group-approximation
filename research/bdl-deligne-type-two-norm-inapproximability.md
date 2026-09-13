---
rg: 2
id: bdl-deligne-type-two-norm-inapproximability
kind: claim
title: Stability in a smaller unitarily invariant norm forbids approximation in a larger one when an order-two element lies in the finite residual
distinct_from:
  mf-hyperlinear-of-finite-normal-quotient: that is Proposition 1.6 of the same paper, converting MF into hyperlinearity along a finite normal kernel; this is Theorem 1.3 and Proposition 1.5, which turn stability in a smaller norm into inapproximability in a larger one.
  schatten-one-models-retaining-mark: that asks for unnormalized Schatten-one models retaining a mark in a Kun--Thom candidate; this is the published obstruction for Deligne-type groups, including the degree-four Deligne cover of Sp_2g(Z) for g at least 3.
---

**ESTABLISHED by citation** (`bdl-deligne-type-two-norm-inapproximability-citation`).
Bachner--Dogon--Lubotzky, *On L^1-approximation of groups*, arXiv:2508.17392v3
(29 Apr 2026).

`||.||_p` is the unnormalized Schatten norm `tr(|A|^p)^(1/p)`. `p = 2` is the
Frobenius norm, `p = infinity` the operator norm, and `||A||_HS = n^(-1/2)||A||_2`.
A finitely generated group is *of Deligne-type* if some central `J` of order two
lies in `ker_RF`, the kernel of the map to the profinite completion.

1. **Theorem 1.3.** Let `Gamma` be of Deligne-type and `1 <= p <= q <= infinity`.
   If `Gamma` is `||.||_q`-stable, it is not `||.||_p`-approximated. Remark 3.1:
   centrality of `J` is never used.
2. **Corollary 1.4 and the paragraph after it.** Some finitely presented groups
   are not `||.||_1`-approximated. By BLSW Theorem 1.3
   (`blsw-real-lattice-frobenius-stability`) and Deligne, the degree-four cover of
   `Sp_(2g)(Z)`, `g >= 3`, is not `||.||_1`-approximated.
3. **Proposition 1.5.** A Deligne-type group that is *operator-HS-stable* is not
   MF. Operator-HS-stable means every operator-norm asymptotic homomorphism is
   pointwise HS-close to genuine homomorphisms.
4. **Proposition 1.7.** Let `N` be a finite normal subgroup with `Gamma/N`
   `||.||_q`-approximated, `p <= q`. If `Gamma` is `||.||_p`-approximated, then it
   is `||.||_q`-approximated.
5. **Conjecture 1.8.** If `H^2(Gamma, V) = 0` for every unitary representation
   `V`, then `Gamma` is operator-HS-stable.

**Status statements in the source.** Whether all groups are sofic, hyperlinear
or MF remain "three major open problems". The authors refer to Dogon (Math. Z.
305, 2023) "for efforts to prove that *real* Deligne central extensions are not
hyperlinear". So as of April 2026 this literature does not decide
hyperlinearity of the real Deligne covers.

**Mechanism, and why it stops short of the normalized norm.** Round `phi_n(J)`
to an exact involution `U_n` (their Lemma 2.2, valid in every unitarily
invariant norm). If `U_n != 1`, it has an eigenvalue `-1`, so
`||U_n - 1||_q >= ||U_n - 1||_op = 2` for every `q`. Stability in `||.||_q` then
produces genuine representations not killing `J`, and Malcev's theorem gives a
contradiction. In the normalized HS norm a single eigenvalue `-1` costs only
`2 n^(-1/2)`. So this two-norm argument cannot reach hyperlinearity unless a
positive fraction of the spectrum is forced away from `1`. That forcing is the
content of `deligne-central-mark-hs-collapse`.

Consumer: `deligne-symplectic-covers-are-not-schatten-approximated`. It extends
item 1 to central finite-residual elements of any finite order.
