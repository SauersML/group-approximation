---
rg: 2
id: affine-leavitt-source-saturated-reynolds-checksum
kind: claim
title: Force one source-saturated cross-typed Reynolds checksum on the marked Leavitt carrier
distinct_from:
  paired-same-reservoir-boundary-lemma: that asks for a branchwise reservoir-or-boundary decomposition through arbitrary fixed depth; this asks for one scalar first-refinement checksum and uses the fixed source/target superrank gap immediately.
  one-coarse-to-fine-prefix-isometry-closes-the-reservoir: that asks for one physical rectangular coefficient between authenticated minimal prefix corners; this asks for one adjoint Gram contraction between packet commutant ranges and avoids wordizing the fine physical selector.
  one-common-intertwiner-carries-the-four-pauli-pi-bridge: that transports four target operators through one almost-unitary physical intertwiner; this transports only one adjoint overlap scalar and does not reconstruct a physical factor or its spectator.
  balanced-controlled-whitehead-return-checksum: that computes a rank gap for the controlled-reflection extension of one two-qubit packet; this uses the actual source-versus-two-child Leavitt Weyl packets with superranks `p^(-2)` and `p^(-4)`.
  canonical-marked-reynolds-return-is-subgroup-intersection: that computes every fixed group-word actuator in the canonical marked trace and rules out source saturation for all of them; this explicitly requires a nonlinear matrix-coordinate actuator instead.
  leavitt-forward-morita-polar-misses-reynolds-return: that computes the polar of the native forward coefficient chart and shows it is either gauge-uncontrolled or the exact label-amplifying rectangular escape; this requires a reverse cross-typed return Gram instead.
---

**OPEN; MINIMAL CROSS-TYPED LEAVITT TARGET.**  In every sufficiently accurate
canonical normalized-HS microstate of the affine-Leavitt Steinberg
presentation, spectrally select the prescribed nontrivial phase carrier `P`
of the marked order-`p` root.  Exactify on `P` the fixed depth-zero source
Heisenberg packet and depth-one two-child packet, and let `R_s,R_t` be their
adjoint Reynolds projections on `End(PH)`.

From the finite matrix tuple construct an approximation-dependent contraction
`X_U` between the two adjoint Reynolds ranges,

```text
X_U=R_t X_U R_s,            ||X_U||_op<=1,
tr_(ad,P)(X_U^*X_U)>=p^(-2)-omega(delta,sep).           (ASR1)
```

where `omega(delta,sep)->0` as the fixed presentation defect and fixed
canonical trace-window error tend to zero.  The trace in `(ASR1)` is
normalized on `End(PH)`.  Equivalently one may use the ambient adjoint trace
and multiply the right side by `tr(P)^2`; marked separation supplies a fixed
positive lower bound for `tr(P)`.

The endpoint is complete and dimension independent.  Since the range of
`X_U` lies in `Ran(R_t)`, finite rank always
gives

```text
tr_(ad,P)(X_U^*X_U)<=tr_(ad,P)(R_t)=p^(-4),             (ASR2)
```

so `(ASR1)--(ASR2)` contradict sufficiently small defect by the fixed amount
`p^(-2)-p^(-4)`.  No pointwise reconstruction of either commutant is
required after `X_U` has been constructed.  This source-Gram trace is weaker
than constructing an adjoint unitary: if such a unitary `T_U` is available,
one simply takes `X_U=R_tT_UR_s`.

The actuator cannot be `Ad(U(w))` for a fixed word `w`, nor a fixed finite
convex average of word actuators.  In that case the overlap expands into
fixed squared word traces, and
`canonical-marked-reynolds-return-is-subgroup-intersection` gives the
canonical limit at most `p^(-4)`.  Thus `(ASR1)` specifically asks for a
nonlinear finite-coordinate extraction—such as the compressed polar/Gram map
of a returned mixed coefficient—whose construction error is bounded by the
named word defects.  This operation must have no functorial counterpart in
the exact regular representation.

The direction in `(ASR1)` is load bearing.  Replacing its right side by
`p^(-4)-o(1)` gives target saturation, which is exactly realized by the
rectangular counterpacket in
`target-saturated-reynolds-return-does-not-lock-leavitt-reservoir`.

All presently named typed Steinberg triangles fail to imply `(ASR1)`:
`mixed-steinberg-loops-admit-morita-rectangular-model` satisfies them while
keeping the two object identities distinct.  Thus the missing compiler must
extract source saturation from a genuinely finite-matrix feature of the
full presentation, or pay its failure as boundary leakage.  More typed
associativity loops, separate PI fingerprints, fixed word returns, and
preservation of every target invariant remain below the exact countermodel.

The first explicit polar candidate is now refuted.
`leavitt-forward-morita-polar-misses-reynolds-return` applies
the native coefficient formula `A |-> sum_i x_iAy_i`.  Typed multiplication
gives it an exact algebraic inverse but does not control its Hilbert adjoint,
because arbitrary nonunitary target-object gauges preserve every coefficient
relation.  After choosing a unitary gauge its polar is already an exact
isometry, but it maps the source label algebra into the doubled target label
algebra—the rectangular escape direction.  It does not map the larger source
commutant into the smaller target commutant.  The live `X_U` must therefore
come from a mixed **return** Gram which reverses the Morita arrow on the
multiplicity coordinate, not from polarizing the forward `Phi` chart.
