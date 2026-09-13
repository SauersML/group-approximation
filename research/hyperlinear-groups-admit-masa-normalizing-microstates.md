---
rg: 2
id: hyperlinear-groups-admit-masa-normalizing-microstates
kind: claim
title: Every hyperlinear group has regular HS microstates that approximately normalize a full masa
distinct_from:
  hyperlinear-implies-sofic: that is the group-approximation statement; this is the frame-existence statement that the soft-kernel split proves equivalent to it, with the U(1)-phases of the frame's normalizers allowed arbitrary, so what it asks of a proof is only an approximately invariant frame.
  invariant-cartan-completion: that asks a prescribed Bernoulli lamp algebra of the Kun--Thom crossed product to sit inside an invariant diagonal ultraproduct; this asks, for an arbitrary hyperlinear group, for some frame and some microstates, with nothing prescribed.
  regular-character-markovization: that asks for doubly stochastic kernels on a hidden state space with trace separation; this asks for a masa normalized by the microstate, whose dephased kernels are then permutations and whose trace defect sits on an abelian normal subgroup.
artifacts:
  - research/artifacts/ex-q34-frame-extraction-2026-09-12.md
---

**OPEN (equivalent to Q3.4 affirmative).**  For every hyperlinear group `G`,
every finite window `F` and every `eps > 0` there are `n`, unitaries
`U_g in U(n)` (`g in F`) and an orthonormal basis with diagonal masa `D_n`
such that

```text
||U_g U_h - U_(gh)||_2 < eps,   |tr U_g| < eps  (g != e),
def_D(U_g) = sup_(f=f* in D_n, ||f||<=1) ||U_g f U_g^* - E_D(U_g f U_g^*)||_2 < eps.
```

Equivalently (`diagonal-normalizer-rigidity`), `G` has regular HS models in
`U(1) wr S_n`: permutations carrying arbitrary phases.

**Why this is the right form of the collapse.**
`block-monomial-hs-models-sofic-mod-amenable-soft-kernel` shows the phases of
a monomial model separate at most an abelian normal subgroup.  `G * Z` has no
such subgroup and is hyperlinear when `G` is.  So this claim for all
hyperlinear groups implies `hyperlinear-implies-sofic`
(route `hyperlinear-implies-sofic-via-frame-extraction`).  The converse is
immediate, because permutation matrices normalize `D_n`.  What is removed is
every difficulty about phase cancellation, `U(1)`-cocycles and dephasing
interference.  What remains is only an approximately invariant frame.

**Model test.**  By `leavitt-units-admit-no-bounded-block-monomial-hs-model`,
the Leavitt unit group has no such microstates.  So a proof of this claim for
any class containing `EL_9(L_(F_2)(1,2))` would prove that group
non-hyperlinear.  Every known sofic group satisfies it, trivially.

## Attempts

- **Fixed-basis dephasing.**  Dead: `dephasing-destroys-multiplicativity`.
  `dephasing-inverse-forces-monomial` shows that one-basis dephasing respects
  inverses only near the monomial locus, which is this claim in the given
  basis.
- **Fresh random intermediate bases.**  Dead: `haar-random-basis-depolarization`.
- **Spectral frames.**  Diagonalizing one `U_g`, or the joint spectral PVM of
  an abelian subgroup after `all-abelian-uniform-hs-rounding-gives-global-pvm`,
  gives a frame normalized by that subgroup only.  The whole content lies in
  coupling frames across non-commuting generators.
- **Round the given microstate in the same dimension.**  Cannot work for `F_2`
  (sketch, unreviewed).  Frame-coherent pairs `(W M_1 W^*, W M_2 W^*)` in
  `U(n)^2` are covered by `(C/eps)^(n^2) e^(O(n log n))` HS-balls of radius
  `O(eps)`, whose total Haar measure is at most `(C' eps)^(n^2) e^(O(n log n))`.
  Haar-random pairs are free microstates, so almost every microstate of `F_2`
  stays a fixed HS distance from every frame-coherent pair.  Frame extraction
  must *choose* microstates; it cannot be a rounding of arbitrary ones.  The
  same count applies wherever 1-bounded entropy is positive.
- **Balanced tensor frames.**  In `U ⊗ conj(U)` the product frame
  `e_i ⊗ conj(e_j)` is normalized only if `U` already is.  The maximally
  entangled vector is exactly invariant, but one vector is not a frame.
- **Kazhdan integrality.**  `kazhdan-almost-centralizers-round-in-finite-actions`
  rounds centralizers *inside* permutation models.  It presupposes the frame.
