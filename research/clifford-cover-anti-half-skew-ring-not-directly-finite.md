---
rg: 2
id: clifford-cover-anti-half-skew-ring-not-directly-finite
kind: claim
title: The anti-central Clifford skew group ring of some Kun--Thom Clifford cover is not directly finite
distinct_from:
  ternary-anti-invariant-swap-corner-is-full: that is a corner problem in the anti-central summand of the ternary Leavitt unit group algebra; this is direct finiteness of a skew group ring over a Clifford-type lamp algebra with a compressing coset action.
  kun-thom-wreath-stably-finite: that is stable finiteness of the untwisted wreath group algebras; this is the twisted anti-central factor, which that theorem does not cover.
artifacts:
  - research/artifacts/clifford-cover-surjunctivity-test-host-2026-09-12.md
---

**OPEN.** For the Kun--Thom Theorem E pair and some `G`-invariant graph `S` on `X = G/Gamma`, the skew
group ring `A_S` of `clifford-cover-group-algebra-splits-into-wreath-and-skew-ring` contains
`a, b` with `b a = 1 != a b`.

## Attempts

- **Why it is not already excluded.** The landed linear theorem
  `rf-lamps-preserve-stable-finiteness-for-arbitrary-actions` inducts through site projections onto
  matrix algebras over stabilizer group algebras.
  - For the complete graph the lamp algebra is the infinite Clifford algebra over `F_3`. It is a directed
    union of central simple algebras `M_(2^k)(F_3)`, hence simple and infinite-dimensional.
  - So it has no algebra maps onto finite site pieces, and the induction has nothing to project to.
- **Obstructions still standing.** The normalized trace of the Clifford algebra is `G`-invariant, which
  gives an `F_3`-valued trace on `A_S`. A defect must have trace `0` mod 3. This constrains but does not
  forbid.
- **Where a construction must get its room.**
  - Compression `u Gamma u^-1 < Gamma` gives an equivariant non-injective self-map of `X`. Its fibers have
    size `[Gamma : u Gamma u^-1]`, which is infinite for the Theorem E pair, so no finite lamp product
    implements it.
  - A witness needs a mechanism other than a finite-fiber site map, for example isometry-like elements
    built from lamp unitaries along the orbit structure of `u`.
- **Support filter (artifact Section 4.1).** Let `a, b` be a witness pair whose supports involve only
  group elements in `Vtilde_S semidirect H` for a subgroup `H <= G`. If `Vtilde_S semidirect H` is sofic,
  then `F_3[Vtilde_S semidirect H]` is stably finite (`linear-sofic-group-algebra-is-stably-finite`; sofic
  implies linear sofic). Its anti-central factor contains the pair, which is a contradiction. So any
  witness generates `H` with `Vtilde_S semidirect H` not sofic. In particular `H` is nonamenable, since
  `Vtilde_S` is locally finite.
- **The naive spinor model fails (artifact Section 4.2).** A Hamming-sofic approximation of the site
  action does not give rank models of `A_S` by the obvious construction.
  - Automorphisms of `Cl(V_n)` permuting sites are implemented on the spinor module by operators.
  - Even a transposition of two sites is implemented by an element like `1 + c_v c_w`, whose distance to
    `1` has full normalized rank.
  - So Hamming-small defects of the site permutations become rank-large defects in the model.
  - Rank models of `A_S` would need a different carrier than spinor modules of finite site pieces. This is
    where linear soficity of the Clifford cover itself is undecided.
- **Only odd characteristic can carry a witness.** Over `F_2` the kernel `(1 + eps)F_2[E_S]` is square-zero, so `F_2[E_S]` is stably finite with `F_2[W]`. For each odd prime `p` the central idempotents `(1 +- eps)/2` give `F_p[E_S] = F_p[W] x A_S^(p)`. So the linear question is this anti-central factor at some odd `p`, and `F_3` is the first case.
