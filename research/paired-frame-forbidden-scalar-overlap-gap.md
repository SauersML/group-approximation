---
rg: 2
id: paired-frame-forbidden-scalar-overlap-gap
kind: claim
title: One scalar Reynolds overlap detects the paired-frame forbidden sector
distinct_from:
  support-packet-covariant-wedderburn-detector: that proves a universal adjoint-HS separation between the two forbidden commutant algebras; this extracts the exact one-scalar ceiling and contrasts it with full allowed overlap.
  adjoint-reynolds-return-needs-one-overlap-moment: that gives an abstract sufficient overlap inequality for nested Schur packets; this computes the sharp overlap gap for the explicit equal-rank paired support frame.
  finite-edge-reynolds-overlap-follows-character-transport: that determines which conditioned character carrier a finite HNN edge can overlap; this first computes how much overlap would distinguish the correct paired carriers if ownership were enforced.
---

Use the seven-dimensional coefficients `V_+,V_-` of
`support-packet-covariant-wedderburn-detector`.  On a selector sector `k`,
let `R_+(k),R_-(k)` be the Reynolds projections onto the two diagonal-packet
commutants on the adjoint space, and for a unitary `W` put

```text
Theta_k(W)=tr_ad(R_+(k) Ad_W R_-(k) Ad_W^* R_+(k)).   (PFO1)
```

For every allowed `J=-1` sector `k in {100,110,111}`, there is a unitary
`W_k` for which

```text
Theta_k(W_k)=tr_ad(R_+(k))=tr_ad(R_-(k)).              (PFO2)
```

On the forbidden sector `k=101`, after arbitrary common multiplicity
amplification by `m`, both Reynolds projections have normalized rank

```text
tr_ad(R_+(101))=tr_ad(R_-(101))=25/784,                (PFO3)
```

but every unitary `W` satisfies the sharp scalar ceiling

```text
Theta_101(W)<=17/784.                                  (PFO4)
```

Equivalently, every attempted forbidden return leaks at least

```text
tr_ad(R_+(101))-Theta_101(W)>=1/98.                    (PFO5)
```

The constants are independent of `m`.  Thus the explicit paired support
packet already solves the local self-hash problem at the scalar level: one
adjoint overlap is perfectly satisfiable on every allowed sector and has a
fixed forbidden gap.  What it does not solve is ownership of the returned
carrier.  Every finite edge identification transports the hard character
`101` to the reverse reservoir `011`, so a global actuator still has to
exclude that character escape.
