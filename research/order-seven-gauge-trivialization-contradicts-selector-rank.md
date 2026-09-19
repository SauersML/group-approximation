---
rg: 2
id: order-seven-gauge-trivialization-contradicts-selector-rank
kind: claim
title: Trivializing the order-seven stage gauge contradicts each exact selector row, so the moving-multicut and six-bridge holes are only vacuously provable
artifacts:
  - research/order-seven-gauge-trivialization-selector-rank-proof.md
  - experiments/order-seven-gauge-kill-2026-09-17/verify_trivial_gauge_rank_floor.py
distinct_from:
  native-cross-gram-conclusions-fail-in-every-tracial-model: that kills the two-row cross-Gram gauge lock via TSG6 and needs a positive overlap of both native transports; this kills the one-row conclusion D_i=1 of the order-seven cone, with no overlap, no second row and no cross-Gram step.
  two-shared-gauge-selector-rows-have-an-affine-rank-obstruction: that is the abstract matrix inequality comparing two rows with one gauge; this specializes one row to a trivial gauge and applies it to the stated outputs of GMI and ESB.
  order-seven-moving-cuts-realize-both-affine-profiles: that is one exact countermodel to deriving the ungauged typing from the heads; this proves that the ungauged typing plus the row is inconsistent in every model, so no model can be found where the order-seven route closes nonvacuously.
  moving-order-seven-stage-gauges-have-coboundary-drift: that shows stage gauges may drift when only charts are typed; this shows the drift is forced, since the undrifted outcome D_i=1 violates the row rank.
---

**ESTABLISHED DICHOTOMY (written proof; not Lean-verified).**  Let `(N,tau)`
be any finite von Neumann algebra (in particular any normalized matrix
algebra).  On a carrier `H tensor M`, let `C_q=1-2F_q` be a label reflection
with `tau(F_q)=q`, let `D` be a reservoir involution, let `R=1-2E` be a
source reflection with `tau(E)=r`, and let `W` be a unitary.  Put
`delta=||WRW^*-C_q tensor D||_2`.  Then

```text
|r-q| <= delta/2 + |2q-1| ||1-D||_2^2/4.                 (OGT1)
```

For the two native selector rows this reads

```text
row 1 (r,q)=(1/2,1/4):  delta_1 + ||1-D_1||_2^2/4    >= 1/2,   (OGT2)
row 2 (r,q)=(1/4,1/8):  delta_2 + (3/8)||1-D_2||_2^2 >= 1/4,   (OGT3)
```

and, from the projection form `(TSG8)`,

```text
delta_1^2 >= 1-||1-D_1||_2^2/2,
delta_2^2 >= 1/2-(3/4)||1-D_2||_2^2.                      (OGT4)
```

Both `(OGT2)` and `(OGT3)` are attained by the exact OAP gauges:
`theta=1/2`, `||1-D_1||^2=2` and `theta=5/6`, `||1-D_2||^2=2/3`, each with
`delta=0`.

**Consequences.**  An exact or `o_2(1)` selector row forces
`||1-D_1||_2^2>=2-o(1)` or `||1-D_2||_2^2>=2/3-o(1)`, row by row.  Hence:

1. **GMI.**  `growing-multicut-el20-order-seven-inheritance` demands that
   `E_0` retain the native selector meaning of row `i` with multiplicity
   involution `D_i`, and concludes `D_i=1+o_2(1)` by `(GMC3)`.  By
   `(OGT2)`/`(OGT3)` these two clauses are jointly false in every model, for
   each row separately.  GMI is therefore equivalent to the nonexistence of
   the models it quantifies over, i.e. to the EL20 endpoint.
2. **ESB.**  Through the established six-square lock `(SGL5)--(SGL7)`, the
   six-exit telescope and the order-seven anchor (the route
   `six-moving-squares-give-el20-multicut`), any output of
   `el20-six-moving-coefficient-square-bridges` produces `D_i=1+o_2(1)` on the
   same `E_0`.  ESB is therefore also only vacuously satisfiable.
3. **Word searches die at ESB2.**  ESB asks for EL20 words whose errors are
   charged to a fixed ordinary-relator menu with dimension-free constants.
   Suppose the construction of `E_0`, the charts and the rows is valid in an
   exact tracial model (the left regular representation `lambda` into
   `L(Delta)`, or any exact `pi`), as the class kill
   `native-cross-gram-conclusions-fail-in-every-tracial-model` records for
   the native packets.  Then every relator defect is zero there, so such a
   word would give exact `(ESB1)--(ESB3)` and hence `D_i=1`, against
   `(OGT2)`.  So no EL20 coefficient word with relator-charged estimates
   satisfies `(ESB2)`.  This explains uniformly the recorded result that
   every candidate bridge "retains a gauge".

## Obstruction (class killed)

The class is every direct proof of the order-seven moving-multicut cone.
That means GMI, ESB and the route
`order-seven-growing-multicut-gives-el20-native-cross-gram`, whether by
coefficient-word search, moving cuts, Fano, Hecke or Leavitt compressions,
or extra returns.

- **Invariant.**  The positive spectral fraction
  `theta(D)=tau((1+D)/2)=1-||1-D||_2^2/4` of the selector multiplicity
  involution.  It is a unitary-conjugacy invariant, and each native row pins
  it to `1/2` (row 1) or `5/6` (row 2) up to `delta/2`.
- **Step where every member dies.**  The gauge-trivialization step.  This is
  `(GMC3)`, "since `D_i^2=1` conclude `D_i=1`", or equivalently the
  ungauged typing `(ESB2)` together with `(ESB3)`.  Trivial gauge means
  `theta=1`, and then `Phi_q(1)=q!=r`.
- **Scope.**  Lock designs of both kinds are now dead.  Conjugating locks
  (one shared gauge for both rows) die by `(TSG6)`.  Trivializing locks (one
  row, stage gauge forced to `1`) die by `(OGT2)`/`(OGT3)`.

**Dichotomy and caveat (H).**  The kill uses hypothesis (H): the `D_i` that
`(GMC3)` trivializes is the selector-row multiplicity involution on `E_0`,
which is how GMI states it and how `(OAP4)` models it.  If (H) fails, the
initial cut does not carry the selector meaning that the downstream route
consumes.  The route to the native cross-Gram premise then either fails as
written or falls under Step 2 of the native cross-Gram class kill.  Either
way the order-seven cone is not a nonvacuous decomposition.  A correct proof
must feed a non-tracial input, such as operator-norm integrality, into the
cone before `(ESB2)`.  Further word search inside the relator-charged
normalized-HS framework cannot succeed.  No Property `(T)` is used.
