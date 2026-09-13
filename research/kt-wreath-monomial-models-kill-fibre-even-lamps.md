---
rg: 2
id: kt-wreath-monomial-models-kill-fibre-even-lamps
kind: claim
title: Every monomial Hilbert--Schmidt model of the Kun--Thom wreath kills all fibre-even lamps, so its monomial radical equals its sofic radical
distinct_from:
  block-monomial-coordinate-collapse: that excludes block-monomial models in which every lamp is diagonal; this shows every block-size-one model kills the whole sofic radical, whatever part of the lamp module is diagonal.
  block-monomial-hs-models-sofic-mod-amenable-soft-kernel: that proves a general group is sofic modulo the soft kernel of such a model; this computes the model kernel for the Kun--Thom wreath and shows the soft kernel is never faithfully represented.
  kt-double-admits-no-bounded-block-monomial-hs-model: that is the double, where trivial amenable radical settles every bounded block size at once; this is the wreath, which is abelian-by-sofic, so the soft-kernel split says nothing and Kun--Thom 4.1 has to act on the soft lamps.
  kun-thom-wreath-sofic-radical-is-fibre-parity-kernel: that is the group-level sofic radical; this shows monomial HS models with arbitrary U(1) phases have the same radical.
artifacts:
  - research/artifacts/ex-q34-kt-wreath-soft-kernel-2026-09-13.md
  - research/artifacts/ex-q34-kt-wreath-soft-kernel-part2-2026-09-13.md
---

**ESTABLISHED** (unreviewed).  Let `Gamma = EL_r(R_+) < G = EL_r(R) x| SL_d(Z)`
be the Kun--Thom Theorem E pair (`r, d >= 3`, any `q`), `N = EL_r(R)`,
`P = F_2[G/Gamma]`, `W = P x| G`, and `K_even <= P` the configurations meeting
every fibre of `G/Gamma -> G/N` evenly.  A monomial HS model is a homomorphism
`rho : W -> prod_omega (U(1) wr S_n)` into the tracial ultraproduct of
monomial unitaries.  No trace condition is assumed.

**Theorem.**  Every monomial HS model of `W` kills `K_even`, so it factors
through the residually finite quotient `W_N = F_2[G/N] x| G`.  Hence

```text
∩ { ker rho : rho a monomial HS model of W }  =  K_even  =  Rad_sof(W).
```

The same holds for every lamp quotient `W/U` with `U <= K_even`, with
`K_even/U` in place of `K_even`.  This includes the intermediate coset wreaths
`W_K`, `Gamma <= K <= N`.

**Proof in four moves** (part 2 artifact, Theorem 7).
1. The permutation part of any block-monomial model has sofic image, so it
   kills `Rad_sof(W) = K_even`.  For block size `1`, `rho(K_even)` is diagonal.
2. Every finite set of cosets in `N/Gamma` is fixed by a conjugate
   `s Gamma(m^k) s^(-1)` of a congruence subgroup, with `s` a positive
   substitution.  This conjugate is Kazhdan and infranormal, with normal
   closure `N`.  So each pair `e_Gamma + e_(h Gamma)` centralizes such a
   subgroup.
3. By `soft-kazhdan-central-elements-fixed-by-normal-closure` (Kun--Thom 4.1,
   through the phase-blind covariance of diagonals),
   `f(h) = rho(e_Gamma + e_(h Gamma))` satisfies `f(h h') = f(h) f(h')`.
4. `N` is perfect, so `f = 1`.  Conjugating by `G` kills every fibre pair.

**Corollaries.**
- No monomial HS model of `W` is injective.  `W` has no regular monomial HS
  model, and, through `diagonal-normalizer-rigidity`, no regular HS microstates
  that approximately normalize a full masa.
- **Partly-soft models do not exist.**  Whatever submodule of lamps is diagonal
  contains `K_even`, and the model is trivial on `K_even`.  This settles the
  model test left open on `monomially-hyperlinear-groups-are-sofic`, which
  predicts no regular monomial model of `W`.
- **Question 3.4.**  The Kun--Thom wreath is fenced like the binary Leavitt
  unit group and the `q = 2` double: any hyperlinear model of `W` is
  frame-incoherent (`hyperlinear-implies-sofic-via-frame-extraction`).
- **U(1) phases buy nothing here.**  A monomial model sees exactly the lamp
  configurations some permutation model sees.

**An earlier, weaker form** (part 1 artifact, Theorem 3): a nonzero
`Gamma`-invariant fibre-even configuration from a finite `Gamma`-orbit in the
fibre of a positive compressor, with `rho(u + n.u) = 1`.  It remains correct,
and the theorem above supersedes it.

**Scope.**
- The trust surface of arXiv:2608.06222 travels with this claim through
  `normal-closure-fixes-gamma-fixed-algebra` and `kun-thom-nonsofic-wreath`.
- Block size `k >= 2` is not covered.
- Nothing here says `W` is not hyperlinear.

Derivation: `kt-wreath-monomial-models-kill-fibre-even-lamps-proof`.
