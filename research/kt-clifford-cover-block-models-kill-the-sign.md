---
rg: 2
id: kt-clifford-cover-block-models-kill-the-sign
kind: claim
title: Every bounded-block monomial HS model of a Kun--Thom Clifford cover kills the central sign and the fibre-even lamps
distinct_from:
  kt-wreath-monomial-models-kill-fibre-even-lamps: that is the binary coset wreath, whose soft kernel is abelian; this is its central Clifford extension, whose soft kernel at the sign -1 is noncommutative, so Pauli-type internal blocks had to be excluded separately, which a tensor square does.
  kun-thom-clifford-cover-weakly-sofic: that proves the Clifford cover weakly sofic and not sofic; this excludes every frame-coherent bounded-block Hilbert--Schmidt model of it, trace-free.
  invariant-graph-clifford-phase: that constructs the family, its tracial model with Clifford lamp algebra, and the sign detector; this shows that no bounded-block monomial model can carry the sign.
artifacts:
  - research/artifacts/ex-q34-kt-wreath-soft-kernel-part4-2026-09-13.md
---

**ESTABLISHED** (unreviewed).  Let `Gamma < G` be the Kun--Thom Theorem E pair,
`N = EL_r(R)`, `X = G/Gamma`, and `S` a `G`-invariant graph on `X` containing
the marked pair `{o, y}` of `invariant-graph-clifford-phase`.  Let
`Wtilde_S = Vtilde_S x| G` be the Clifford cover: `Vtilde_S` is the central
`F_2`-extension of `F_2[X]` with commutator form `b_S` and center sign `z`.

**Theorem.**  For every fixed `k`, every homomorphism
`rho : Wtilde_S -> prod_omega (U(k) wr S_n)` kills `z` and the preimage
`Ktilde_even` of the fibre-even configurations.  Consequently:
- `Wtilde_S` has no regular HS model in `U(k) wr S_n` for any fixed `k`, and
  no regular microstates approximately permuting a bounded-rank frame;
- any hyperlinear model of a Clifford cover is frame-incoherent, like those of
  the wreath, the `q = 2` double and the Leavitt units.  This bears on
  `clifford-cover-hilbert-embeddable-route`.

**Proof in four moves** (part 4 artifact, Theorem 12).
1. **Soft sign.**  `z` is the image of the marked word, which lies in the
   sofic radical.  So `rho(z)` is a block-diagonal central involution.
   Restrict to the invariant corner where `rho(z) = -1`, stratified by rank.
2. **Tensor square.**  `rho ⊗ conj(rho)` on that corner sends `z` to `1`, so
   it is a bounded-block model of the wreath `W`.  By
   `kt-wreath-monomial-models-kill-fibre-even-lamps` it kills `K_even`.  Since
   `||X ⊗ conj X - 1||_2^2 = 2 - 2 |tr X|^2`, every lift of a fibre-even lamp is
   a scalar on the corner.
3. **Odd pairing.**  The invariant graph pairs two fibre-even lamps oddly.
   Otherwise its edges inside the fibre form an `N`-invariant cut, and
   perfectness of `N` makes the cut trivial.  Their lifts anticommute, and
   scalars commute, so the corner is `0`.
4. **Descent.**  `rho(z) = 1`, `rho` factors through `W`, and the wreath
   theorem kills `K_even`.

**Scope.**
- Trust surface of arXiv:2608.06222, through the wreath claim.
- Unbounded blocks are not covered, and cannot be: the Clifford lamp algebra
  of `invariant-graph-clifford-phase` item 3 is a hyperfinite tracial model
  with unbounded blocks.
- Nothing here says a Clifford cover is not hyperlinear.

Derivation: `kt-clifford-cover-block-models-kill-the-sign-proof`.
