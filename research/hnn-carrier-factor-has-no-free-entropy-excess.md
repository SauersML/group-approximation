---
rg: 2
id: hnn-carrier-factor-has-no-free-entropy-excess
kind: claim
title: The carrier HNN factor is entropy-starved - its amalgamated free product structure is invisible to 1-bounded entropy
artifacts:
  - research/artifacts/coset-wreath-cartan-entropy-2026-08-22.md
distinct_from:
  hnn-carrier-factorial-character-collapse: that node remarks strong 1-boundedness of one ENEMY GNS factor via wq-normality inside the collapse hole; this is the unconditional entropy ceiling for the carrier's own REGULAR trace, recorded as a fence: no excess-entropy route can be built on the carrier side, so the entropy attack lives only on the wreath.
  coset-wreath-hyperlinearity-forces-strong-one-boundedness: that is the entropy ceiling for the wreath, proved through the lamp Cartan; this is the ceiling for the HNN carrier, proved through commensuration quasi-normalizers with no Cartan and no freeness input, and its role is opposite - it KILLS a route shape rather than opening one.
---

Let `n >= 3`, `Lambda = SL_n(Z) <= Gamma = SL_n(Z[1/p])`,
`H = < Gamma, t | [t, Lambda] = 1 >` the carrier, `L(H)` its group von
Neumann algebra with the regular trace, so `L(H) = L(Gamma) *_{L(Lambda)}
(L(Lambda) tensor L(Z))`.  Claim (THEOREM):

```text
h(L(H)) <= h(L(Lambda)) = 0,                                      (CE0)
```

`h` being Hayes' 1-bounded entropy.  Hence if the carrier `H` is
hyperlinear (the kernel-loop question: amalgamation permanence over the
(T) subgroup), then `L(H)` is strongly 1-bounded and every generating
tuple has `delta_0 <= 1`.

*Proof.*  `B = L(Lambda)` is a diffuse II_1 subfactor.  (i) For every
`gamma in Gamma`, commensuration (`[Lambda : Lambda cap gamma Lambda
gamma^{-1}] < infinity`) makes `Lambda gamma Lambda` a finite union of
left (and of right) cosets, so `B u_gamma B` is contained in finitely
many `u_{gamma_i} B` (and symmetrically): every `u_gamma` lies in the
quasi-normalizer of `B`.  (ii) `u_t` commutes with `B` elementwise, so
it also quasi-normalizes.  (iii) `u_gamma` and `u_t` generate `L(H)`,
so `L(H) = W^*(qN(B))`.  (iv) Hayes' 1-bounded entropy is monotone
under quasi- (indeed wq-) normalizing generation:
`h(W^*(qN_M(B))) <= h(B)` for diffuse `B` (Hayes, IMRN 2018,
arXiv:1505.06682 — the singular-subspace/wq-normalizer calculus; used
at statement level).  (v) `h(L(SL_n(Z))) = 0` for `n >= 3`: strong
1-boundedness of these group factors is in Jung's example list (GAFA 17
(2007), arXiv:math/0510576, via property (T); also
Hayes–Jekel–Kunnawalkam Elayavalli, arXiv:2107.03278: every property
(T) II_1 factor is strongly 1-bounded), and `>= 0` since `Lambda` is
residually finite hence hyperlinear.  Composing gives (CE0).  QED.

**Consequences.**

1. **Route-shape fence.**  An "excess-entropy" contradiction route on
   the CARRIER (the analogue of `nonhyperlinear-from-lamp-torsor-excess`
   with `H` in place of `W_3`) is impossible: (CE0) is unconditional,
   so no lower bound `h(L(H)) > 0` can ever hold.  Despite `L(H)` being
   an amalgamated free product with a diffuse extra leg, its free
   structure is entropy-invisible — the (T), commensurated base absorbs
   it.  The entropy attack on the goal lives ONLY on the wreath, where
   the lamp Cartan (`coset-wreath-algebra-has-a-lamp-cartan`) plays the
   role commensuration plays here.
2. **Second proof of the wreath ceiling.**  The same argument runs in
   `L(W_3)`: `u_gamma` quasi-normalizes `L(Lambda)` by the identical
   double-coset computation, and the base lamp `k_0` commutes with
   `L(Lambda)` (`Lambda` fixes the base coset), so
   `L(W_3) = W^*(qN(L(Lambda)))` and `h(L(W_3)) <= h(L(Lambda)) = 0` —
   a Cartan-free, freeness-free derivation of
   `coset-wreath-hyperlinearity-forces-strong-one-boundedness` (SB1)
   with a different trust surface (commensuration + (T) instead of
   building geometry + Feldman–Moore + Jung's Cartan case).  The two
   proofs stand independently.
3. Calibration for the excess hole: since the ceiling holds on BOTH
   the carrier and the wreath through `h(L(Lambda)) = 0`, any
   excess-entropy witness must specifically beat the `Lambda`-relative
   absorption — matching the fibration form recorded in
   `coset-wreath-microstates-carry-excess-entropy`.
