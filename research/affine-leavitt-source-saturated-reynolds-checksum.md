---
rg: 2
id: affine-leavitt-source-saturated-reynolds-checksum
kind: claim
title: Force one source-saturated cross-typed Reynolds checksum on the marked Leavitt carrier
distinct_from:
  paired-same-reservoir-boundary-lemma: that asks for a branchwise reservoir-or-boundary decomposition through arbitrary fixed depth; this asks for one scalar first-refinement checksum and uses the fixed source/target superrank gap immediately.
  one-common-intertwiner-carries-the-four-pauli-pi-bridge: that transports four target operators through one almost-unitary physical intertwiner; this transports only one adjoint overlap scalar and does not reconstruct a physical factor or its spectator.
  balanced-controlled-whitehead-return-checksum: that computes a rank gap for the controlled-reflection extension of one two-qubit packet; this uses the actual source-versus-two-child Leavitt Weyl packets with superranks `p^(-2)` and `p^(-4)`.
---

**OPEN; MINIMAL CROSS-TYPED LEAVITT TARGET.**  In every sufficiently accurate
canonical normalized-HS microstate of the affine-Leavitt Steinberg
presentation, spectrally select the prescribed nontrivial phase carrier `P`
of the marked order-`p` root.  Exactify on `P` the fixed depth-zero source
Heisenberg packet and depth-one two-child packet, and let `R_s,R_t` be their
adjoint Reynolds projections on `End(PH)`.

Produce one evaluated mixed return actuator `T=Ad(U(w))`, or a bounded
average of such actuators, for which

```text
Theta=tr_(ad,P)(R_s T^* R_t T R_s)
      >=p^(-2)-omega(delta,sep),                        (ASR1)
```

where `omega(delta,sep)->0` as the fixed presentation defect and fixed
canonical trace-window error tend to zero.  The trace in `(ASR1)` is
normalized on `End(PH)`.  Equivalently one may use the ambient adjoint trace
and multiply the right side by `tr(P)^2`; marked separation supplies a fixed
positive lower bound for `tr(P)`.

The endpoint is complete and dimension independent.  Finite rank always
gives

```text
Theta<=tr_(ad,P)(R_t)=p^(-4),                           (ASR2)
```

so `(ASR1)--(ASR2)` contradict sufficiently small defect by the fixed amount
`p^(-2)-p^(-4)`.  The overlap is a finite average of squared ordinary word
traces, hence no pointwise reconstruction of either commutant is required.

The direction in `(ASR1)` is load bearing.  Replacing its right side by
`p^(-4)-o(1)` gives target saturation, which is exactly realized by the
rectangular counterpacket in
`target-saturated-reynolds-return-does-not-lock-leavitt-reservoir`.

All presently named typed Steinberg triangles fail to imply `(ASR1)`:
`mixed-steinberg-loops-admit-morita-rectangular-model` satisfies them while
keeping the two object identities distinct.  Thus the missing compiler must
extract source saturation from a genuinely finite-matrix feature of the
full presentation, or pay its failure as boundary leakage.  More typed
associativity loops, separate PI fingerprints, and preservation of every
target invariant remain below the exact countermodel.
