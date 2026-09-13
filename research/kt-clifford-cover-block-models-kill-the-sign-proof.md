---
rg: 2
id: kt-clifford-cover-block-models-kill-the-sign-proof
kind: route
title: Tensor the model with its conjugate on the sign corner, make fibre-even lamps scalar by the wreath theorem, and let an odd invariant pairing empty the corner
target: kt-clifford-cover-block-models-kill-the-sign
requires:
  - kt-wreath-monomial-models-kill-fibre-even-lamps
  - invariant-graph-clifford-phase
  - kun-thom-clifford-radical-phase
artifacts:
  - research/artifacts/ex-q34-kt-wreath-soft-kernel-part4-2026-09-13.md
---

Full proof: part 4 artifact, identity (SC), Lemma 13 and Theorem 12.

1. **The sign is soft.**  `kun-thom-clifford-radical-phase` puts the marked word
   `x` in `Rad_sof(H)` for `H = G *_Gamma (Gamma x C_2)`.  By item 2 of
   `invariant-graph-clifford-phase`, `H ->> Wtilde_S` sends `x` to `z` when
   `{o, y} in S`.  So `z in Rad_sof(Wtilde_S)`, the permutation part kills
   `z`, and `rho(z)` is block-diagonal.
2. **Corners.**  `p_- = (1 - rho(z))/2` is block-diagonal and commutes with
   `rho`.  Its blockwise rank is invariant under the permutation part.  On each
   rank stratum of positive measure, `rho_r = p_- rho p_-` is a block-monomial
   model of block size `r` with `rho_r(z) = -1`.
3. **Scalar lamps.**  `rho_r ⊗ conj(rho_r)` has block size `r^2` and sends `z`
   to `1`, so it factors through `W`.  It kills `K_even`
   (`kt-wreath-monomial-models-kill-fibre-even-lamps`).  With
   `||X ⊗ conj X - 1||_2^2 = 2 - 2 |tr X|^2` and
   `||X - tr(X)||_2^2 = 1 - |tr X|^2`, each `rho_r(utilde)`,
   `utilde in Ktilde_even`, is a scalar.
4. **Odd pairing.**  Suppose `b_S` vanished on fibre-even lamps of the fibre of
   `{o, y}`.  Then `1_S(a, c) = f(a) + f(c)` there, with `f = 1_S(o, .)`, a cut.
   `N` maps the cut side `A` to `A` or its complement, a homomorphism
   `N -> Z/2`.  It is trivial since `EL_r(R)` is perfect.  So `A` is
   `N`-invariant, hence `∅` or the whole fibre, and there is no edge `{o, y}`.
   So some `u, v in K_even` have `[utilde, vtilde] = z`.
5. **Conclusion.**  Scalars commute, so `rho_r(z) = 1`, a contradiction.  So
   `p_- = 0` and `rho(z) = 1`.  Now `rho` factors through `W`, and step 3's
   theorem kills `K_even`.
