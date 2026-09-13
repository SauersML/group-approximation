---
rg: 2
id: kt-wreath-monomial-models-kill-fibre-even-lamps
kind: claim
title: Every bounded-block monomial Hilbert--Schmidt model of the Kun--Thom wreath kills all fibre-even lamps, so its monomial radical equals its sofic radical
distinct_from:
  block-monomial-coordinate-collapse: that excludes block-monomial models in which every lamp is diagonal; this shows every bounded-block model kills the whole sofic radical, whatever part of the lamp module is diagonal.
  block-monomial-hs-models-sofic-mod-amenable-soft-kernel: that proves a general group is sofic modulo the soft kernel of such a model; this computes the model kernel for the Kun--Thom wreath and shows the soft kernel is never faithfully represented.
  kt-double-admits-no-bounded-block-monomial-hs-model: that is the double, where trivial amenable radical settles every bounded block size at once; this is the wreath, which is abelian-by-sofic, so the soft-kernel split says nothing and Kun--Thom 4.1 has to act on the soft lamps.
  kun-thom-wreath-sofic-radical-is-fibre-parity-kernel: that is the group-level sofic radical; this shows bounded-block monomial HS models, with arbitrary phases and internal rotations, have the same radical.
artifacts:
  - research/artifacts/ex-q34-kt-wreath-soft-kernel-2026-09-13.md
  - research/artifacts/ex-q34-kt-wreath-soft-kernel-part2-2026-09-13.md
  - research/artifacts/ex-q34-kt-wreath-soft-kernel-part3-2026-09-13.md
---

**ESTABLISHED.**  Review status:
- *Block size 1.*  The combining step (soft lamps, homomorphism, perfectness)
  passed in `research/artifacts/ex-review-groups-2026-09-12-part14.md` §14.3.
- *Bounded blocks.*  The part 3 extension passed at step level in
  `research/artifacts/ex-review-groups-2026-09-12-part16.md` §16.5.  That
  covers Kadison diagonalization into `Z ⊗ D_k`, the partition structure of
  `C`, the equal-size block bijections, the order-preserving `S_k` cocycle,
  `sigma~` implementing `Ad rho` on `C`, and the use of Kun--Thom 4.1 with
  `K_even` as the abelian normal subgroup.
- *Not re-derived in either review.*  Kadison's theorem, Kun--Thom 4.1, the
  deep-congruence lemma, and the artifact lemmas line by line.

Let `Gamma = EL_r(R_+) < G = EL_r(R) x| SL_d(Z)`
be the Kun--Thom Theorem E pair (`r, d >= 3`, any `q`), `N = EL_r(R)`,
`P = F_2[G/Gamma]`, `W = P x| G`, and `K_even <= P` the configurations meeting
every fibre of `G/Gamma -> G/N` evenly.  A block-monomial HS model of block
size `k` is a homomorphism `rho : W -> prod_omega (U(k) wr S_n)`.  No trace
condition is assumed.

**Theorem.**  For every fixed `k`, every block-monomial HS model of `W` kills
`K_even`, so it factors through the residually finite quotient
`W_N = F_2[G/N] x| G`.  Hence, for each `k`,

```text
∩ { ker rho : rho : W -> prod_omega (U(k) wr S_n) }  =  K_even  =  Rad_sof(W).
```

The same holds for every lamp quotient `W/U` with `U <= K_even`, with
`K_even/U` in place of `K_even`.  This includes the intermediate coset wreaths
`W_K`, `Gamma <= K <= N`.

**Proof in four moves** (part 2, Theorem 7; part 3, Theorem 9).
1. The permutation part of any block-monomial model has sofic image, so it
   kills `Rad_sof(W) = K_even`.  Hence `rho(K_even)` is block-diagonal:
   diagonal for `k = 1`.
2. Every finite set of cosets in `N/Gamma` is fixed by a conjugate
   `s Gamma(m^k) s^(-1)` of a congruence subgroup, with `s` a positive
   substitution.  This conjugate is Kazhdan and infranormal, with normal
   closure `N`.  So each pair `e_Gamma + e_(h Gamma)` centralizes such a
   subgroup.
3. By `soft-kazhdan-central-elements-fixed-by-normal-closure` (Kun--Thom 4.1,
   through phase-blind covariance for `k = 1` and a finite atom cocycle for
   `k >= 2`), `f(h) = rho(e_Gamma + e_(h Gamma))` satisfies
   `f(h h') = f(h) f(h')`.
4. `N` is perfect, so `f = 1`.  Conjugating by `G` kills every fibre pair.

**Corollaries.**
- No bounded-block monomial HS model of `W` is injective.  `W` has no regular
  HS model in `U(k) wr S_n` for any fixed `k`.
- Through `diagonal-normalizer-rigidity` and
  `coarse-frame-normalizers-are-near-block-monomial`, no regular HS microstates
  of `W` approximately normalize a full masa.  None approximately permute an
  equal-rank decomposition of bounded rank either.
- **Partly-soft models do not exist.**  Whatever submodule of lamps is
  block-diagonal contains `K_even`, and the model is trivial on `K_even`.  This
  settles the model test left open on `monomially-hyperlinear-groups-are-sofic`.
- **Question 3.4.**  The Kun--Thom wreath is fenced exactly like the `q = 2`
  double: any hyperlinear model of `W` is frame-incoherent, with no
  approximately invariant bounded-rank frame
  (`hyperlinear-implies-sofic-via-frame-extraction`).  Unbounded blocks are
  universal, so this is the threshold.
- **Phases and internal rotations buy nothing here.**  A bounded-block model
  sees exactly the lamp configurations that some permutation model sees.
- **Cartan completion.**  `invariant-cartan-completion` need only place
  `L(K_even)` in a `G`-invariant diagonal ultraproduct.

**Earlier forms.**  Part 1 (Theorem 3) gives a nonzero `Gamma`-invariant
fibre-even configuration `u` from a finite `Gamma`-orbit in a compressed fibre,
with `rho(u + n.u) = 1` for `k = 1`.  It remains correct, and is superseded.

**Scope.**
- The trust surface of arXiv:2608.06222 travels with this claim through
  `normal-closure-fixes-gamma-fixed-algebra` and `kun-thom-nonsofic-wreath`.
- Unbounded block size is not covered, and cannot be.
- Nothing here says `W` is not hyperlinear.

Derivation: `kt-wreath-monomial-models-kill-fibre-even-lamps-proof`.
