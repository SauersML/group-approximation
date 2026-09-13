---
rg: 2
id: kt-wreath-monomial-models-kill-fibre-even-lamps-proof
kind: route
title: Soften the fibre-even lamps through the sofic radical, fix any pair by a deep congruence conjugate, transport along EL_r(R), and kill the resulting homomorphism by perfectness
target: kt-wreath-monomial-models-kill-fibre-even-lamps
requires:
  - kun-thom-wreath-sofic-radical-is-fibre-parity-kernel
  - soft-kazhdan-central-elements-fixed-by-normal-closure
  - kun-thom-nonsofic-wreath
  - diagonal-normalizer-rigidity
artifacts:
  - research/artifacts/ex-q34-kt-wreath-soft-kernel-2026-09-13.md
  - research/artifacts/ex-q34-kt-wreath-soft-kernel-part2-2026-09-13.md
---

Full proofs: part 1 artifact §1--2 (monomial facts, Lemma 1) and part 2
artifact Lemma 6, Theorem 7 and Corollary 8.

1. **Soft lamps.**  The permutation part `psi` of a monomial model is a
   homomorphism, since `d_H <= ||.||_2^2 / 2`.  `psi(W)` is sofic, so `psi`
   kills `K_even` (`kun-thom-wreath-sofic-radical-is-fibre-parity-kernel`).
   Since `||(c; sigma) - (c; id)||_2^2 = 2 d_H(sigma, id)`, `rho(K_even)` is
   diagonal.
2. **Deep congruence conjugates.**
   - `Gamma(m^k) = ker(EL_r(R_+) -> SL_r(R_+/m^k))` is Kazhdan, since it has
     finite index in `Gamma`.
   - It is normalized by `Gamma` and compressed by every nonnegative
     `t in SL_d(Z)`, because `t(m^k) <= m^k`.  These generate `G`, so it is
     infranormal.
   - Its normal closure contains `e_ij(x^a)` for `|a| >= k`, their
     `SL_d(Z)`-translates `e_ij(x^c)` for `c != 0`, and the Steinberg
     commutators `e_ij(1)`.  So it is `N`.
   - For `h in N` with denominators `x^b` and `s` positive, `s(Gamma(m^k))`
     has entries `1 + O(x^(k(1..1)))`.  For `k >= 2 max b`, conjugating by
     `h^(-1)` keeps them polynomial, so `s(Gamma(m^k)) <= h Gamma h^(-1)` by
     Suslin's `SL_r(R_+) = EL_r(R_+)`.
3. **Transport.**  `a = e_Gamma + e_(h' Gamma)` centralizes such a conjugate
   `Lambda`, has trivial permutation part, and `G` is residually finite.
   `soft-kazhdan-central-elements-fixed-by-normal-closure` gives
   `rho(e_(h Gamma) + e_(h h' Gamma)) = rho(e_Gamma + e_(h' Gamma))` for all
   `h in N`.
4. **Homomorphism and perfectness.**  `f(h) = rho(e_Gamma + e_(h Gamma))`
   satisfies `f(h h') = f(h) f(h')`, with values in the abelian group
   `rho(K_even)`.
   - `N = EL_r(R)` is perfect for `r >= 3`, so `f = 1`.
   - Pairs span the fibre-even configurations of `N/Gamma`.
   - Conjugating by `G` covers every fibre, so `rho(K_even) = 1`.
5. **Radical equality.**  `W_N` is residually finite (same radical node,
   part 2), so its permutation models separate points.
6. **Corollaries.**
   - Regular models are injective, so none exist.
   - The finitary masa form follows from clause 1 of
     `diagonal-normalizer-rigidity` and the diagonal argument.
   - Lamp quotients `W/U`, `U <= K_even`, follow by Theorem A of
     `research/artifacts/kun-thom-lamp-quotient-hosts-2026-09-12.md` and the
     same argument on images of pairs.
