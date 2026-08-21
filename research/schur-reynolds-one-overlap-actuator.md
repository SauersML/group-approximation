---
rg: 2
id: schur-reynolds-one-overlap-actuator
kind: claim
title: Force the Schur Reynolds return through one scalar overlap moment
distinct_from:
  compressor-covariant-packet-reynolds-return: that asks for a transported positive-density Reynolds core and a bounded relator-energy payment; this asks only for the scalar lower bound `(ORA1)`.
  s3-active-packet-proper-corner-return: that asks to place the whole reducing active isotypic sum into the next carrier; this authenticates only one adjoint overlap moment.
  hs-schur-toeplitz-root-defect-collapse: that propagates a Toeplitz coefficient defect through Steinberg roots; this starts from the Schur packet Reynolds gap and asks for one context-local infinite actuator.
  ascending-hnn-cannot-create-nonhyperlinearity: that rules out a bare ascending HNN step over a hyperlinear base; this requires BCS-dependent packet covariance beyond a self-embedding stable letter.
artifacts:
  - research/artifacts/crispr-self-hash-compiler-2026-08-20.md
---

OPEN.  Effectively from a Boolean context predicate `f`, extend its fixed
Schur packet inclusion `A_f<=B_f` by finitely many ordinary group generators
and relators, including at least one essentially infinite actuator `t`, so
that the following hold.

1. After fixed-packet HS exactification in every sufficiently accurate finite
   matrix model, the Reynolds projections `R_A,R_B` and
   `T=Ad_(U(t))` satisfy

   ```text
   tr_ad(R_A T^*R_BTR_A)
     >=tr_ad(R_A)-K_f eta,                              (ORA1)
   ```

   with `K_f` independent of matrix dimension.
2. Auxiliary generators are context-local: shared original BCS involutions
   remain the same words, while no new commutation between different BCS
   contexts is imposed.
3. Every exact allowed BCS representation, for which the forbidden
   projection is zero, extends after countable amplification to an exact
   representation of the cell.  The extension may be properly infinite and
   nontracial, and must retain the native Fanizza signal when this cell is
   used in that compiler.

By `adjoint-reynolds-return-needs-one-overlap-moment`, `(ORA1)` yields

```text
q_f^2<=c_f^(-1)K_f eta,                                 (ORA2)
```

so forbidden mass has a dimension-independent vanishing modulus and is
immune to spectator amplification.

## Attempts

- **Bare finite packet: impossible.**  Its regular representation supplies
  stationary finite multiplicity flow.  The actuator must use genuinely
  infinite covariance or a proper-corner coefficient direction.
- **Bare ascending HNN: circular.**  By
  `ascending-hnn-cannot-create-nonhyperlinearity`, a proper self-embedding of
  a hyperlinear base cannot be the first obstruction.  The useful datum must
  be the BCS-dependent overlap `(ORA1)`, not the existence of a stable letter.
- **Universal conjugacy of unequal projections: invalid.**  An abstract
  identity conjugating carriers of unequal tracial size would also constrain
  exact tracial representations and can collapse completeness.  The rank
  mismatch must arise only after finite packet exactification/adjoint
  compression.
- **Live search target.**  Use `(SOM7)` to seek a finite Hecke, PSD, or
  root-character certificate for the single moment lower bound `(ORA1)`.
  This is strictly weaker than termwise covariance of all packet words.
- **Scalar syntax does not remove the geometric load.**  Identity `(SOM3)`
  says the deficit in `(ORA1)` is exactly the total squared leakage
  `||(I-R_B)TR_A||^2`.  Thus the scalar is a compact certificate for the
  whole Reynolds range, not a loophole allowing one favorable adjoint
  vector to stand in for it.
- **Most concrete existing chart.**
  `support-packet-paired-word-frame-exposes-forbidden-rank` names the changing
  Reynolds module by four packet words.  Its only finite-edge escape is the
  forced `101<->011` two-cycle.  The open one-sided reservoir claim can be
  tested against `(ORA1)` directly, avoiding any stronger demand once its
  hard frame is placed.
- **The local scalar detector is already exact.**
  `paired-frame-forbidden-scalar-overlap-gap` proves that the paired frame has
  full scalar overlap on every allowed sector, whereas its forbidden overlap
  is at most `17/784`, leaving the amplification-independent deficit `1/98`.
  Thus no further local checksum invention is needed for this chart.  The
  remaining load is precisely to force the actuator to return into the owned
  carrier instead of the reverse `011` reservoir.
- **Character ownership remains load-bearing.**
  `finite-edge-reynolds-overlap-follows-character-transport` proves that an
  HNN edge carries the conditioned scalar checksum to the induced central
  character and nowhere else.  For the paired frame this is the compulsory
  `101<->011` reservoir.  The actuator must add an infinite label, a
  gauge-doubled logical invariant, or an equivalent nonstationary ownership
  mechanism; merely rewriting the return as one scalar does not remove it.
- **Naive gauge forgetting cancels the detector.**
  `gauge-symmetrizing-hard-pair-cancels-paired-overlap-gap` proves that equal
  gauge-orbit multiplicities on `101` and `011` make the plus and minus
  Reynolds carriers unitarily conjugate after summing the two orientations.
  Gauge doubling remains a valid completeness/covariance device, but the
  actuator must retain the private orientation or decorate it by a
  nonreturning infinite label; conditioning only on the invariant logical
  product is stationary.
