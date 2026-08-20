---
rg: 2
id: toeplitz-tail-retains-contextual-schur-density
kind: claim
title: A contextual Schur head survives or recurses inside the Toeplitz tail commutant
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
---

OPEN. Use the head-tail endomorphism of
`toeplitz-head-tail-unital-self-embedding` and the packet placement of
`schur-child-crosses-toeplitz-compressor` to prove the following uniform
microstate dichotomy.

On a positive-density forbidden packet carrier, either the locally placed
child/full Reynolds difference has a fixed positive-density component in

```text
Comm(alpha(Gamma)) minus Comm(Gamma),                           (TTR1)
```

or the residual `alpha(Gamma)` action which erases that component canonically
contains a new forbidden Schur carrier in the next Toeplitz tail. The carrier
loss and squared transport error must be at most a fixed multiple of the
named normalized-HS relator energy. Iteration must have a contraction factor
strictly below one, independent of matrix dimension and tail depth.

The first branch is paid by
`schur-wall-in-property-t-compressor-pays-hs-energy`; the second is summable
by `contractive-computation-ladder`. This is deliberately stronger than
recovering every externally fixed tail window: the recursion must act on the
same residual coefficient algebra which caused the loss in `(TTR1)`, thereby
excluding the spectator amplification in
`residual-action-can-erase-local-reynolds-density`.

The ring identity `sigma(a)=xay+eps(a)f` is the candidate bounded-cost return:
it reproduces the entire tail in one fixed formula rather than by a word whose
length grows with depth. What remains is to couple the shared BCS selector
projections to that formula using group words.

The head algebra is also finitely actuated:
`toeplitz-tail-plus-one-swap-generates` gives one involution `s` with
`T=<sigma(T),s>`. Therefore no unbounded family of unrelated head generators
is needed. The analytic problem is to make the Schur violation determine the
action of this fixed actuator on the residual multiplicity space.

## Attempts

- Merely place `B_f^Q` in `alpha(Gamma)` and `B_f` in `Gamma`: this dies by
  `residual-action-can-erase-local-reynolds-density`, since the rest of the
  compressed group may act irreducibly on the packet multiplicity.
- Recover every fixed collection of deeper Toeplitz heads: this gives only a
  growing hyperlinear profile; an arbitrary residual spectator can always be
  enlarged after the window is chosen.
- Active attack: use the explicit compression `a |-> y a x` to define the
  next carrier *inside the commutant of the residual action which erased the
  current carrier*. The missing estimate is a dimension-free conditional
  expectation inequality showing that loss of head Reynolds mass produces,
  with a strict contraction, selector mass in that compressed residual
  corner. The single head swap from
  `toeplitz-tail-plus-one-swap-generates` is the candidate bounded word which
  implements this transfer.
- Dinur's preprocess-power-compose architecture is now isolated as
  `hs-schur-packet-gap-amplification`. Classical graph powering supplies the
  needed anti-localization, while Schur packet composition is supposed to
  reset the local matrix scale. The unresolved point is not classical PCP
  soundness; it is synchronization of the contextwise HS exactifications on
  the shared selector words.
