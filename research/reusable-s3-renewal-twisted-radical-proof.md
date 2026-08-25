---
rg: 2
id: reusable-s3-renewal-twisted-radical-proof
kind: route
title: Sum the supercritical recurrence and split automorphic from compressed returns
target: reusable-s3-renewal-is-twisted-radical-or-proper-corner
requires:
  - finite-s3-cross-edge-holonomy-cannot-renew-saturated-escape
  - agent-aggregate-escape-two-intertwiner-clifford-dichotomy
  - agent-aggregate-escape-two-intertwiner-aco4-is-twisted-nonce
  - proper-packet-rank-growth-needs-compressed-two-cell
  - universal-block-return-violates-the-regular-firewall
---

Iterating `(SRD2)` to depth `N` gives

```text
lambda^N a_0
 <=a_N+C sqrt(E) sum_(j=0)^(N-1) lambda^(N-1-j)p(j).
```

Since `a_N<=1`, division by `lambda^N` yields

```text
a_0<=lambda^(-N)
    +C sqrt(E) sum_(j=0)^(N-1) lambda^(-1-j)p(j).       (1)
```

The series

```text
K_(lambda,p)=sum_(j>=0)lambda^(-1-j)p(j)               (2)
```

converges because `lambda>1` and `p` is polynomial.  The same finite
presentation and the same approximate representation support `(SRD2)` for
every `N`, so let `N` tend to infinity in `(1)`.  Then

```text
a_0<=C K_(lambda,p)sqrt(E).                             (3)
```

Combining `(3)` with `(SRD3)` proves `(SRD4)`, with
`C_*=C_0+C K_(lambda,p)`.  This is exactly an HS-radical modulus on the
marked packet corner.

For the exact endpoint, suppose the inverse twisted stabilizer algebra had a
nonzero finite-dimensional representation satisfying the return relations.
Tensor it with the packet implementers `(SRD1)`, cancel the two multipliers,
and induce across the finite packet-type orbit.  By
`agent-aggregate-escape-two-intertwiner-clifford-dichotomy`, this is an exact
finite-dimensional representation of the whole automorphic cell containing
`sigma`.  It has `E=0` and `tr(B_sigma)>0`, contradicting `(SRD4)`.  Hence the
active inverse central character lies in the projective finite-dimensional
radical.

For the robust endpoint, if the twisted regular algebra of `(SRD5)` were
Connes embeddable, its matrix microstates could be tensored with the fixed
packet implementers and induced over the same finite orbit.  The resulting
full-presentation microstates have `E` tending to zero while the marked
packet density stays bounded below by a fixed positive constant.  This
contradicts `(SRD4)`, exactly as in
`agent-aggregate-escape-two-intertwiner-aco4-is-twisted-nonce`.  Thus the
twisted regular algebra is non-CE.

It remains to audit the only stated exception.  If a return ceases to act by
packet automorphisms, exactification decomposes its first nonflat two-cell
into block maps between decoded source and target carriers.  The regular
stationary-flow argument in
`proper-packet-rank-growth-needs-compressed-two-cell` shows that equal-rank
blocks give no rank pressure.  For unequal carriers, cyclic products `YX`
and `XY` have equal matrix trace, so every positive deficit must be paid by
an estimate comparing them with two carriers of unequal trace.  That is the
trace-cyclic proper-corner interface.

Finally, if the two comparisons are universal group-algebra identities, or
are obtained by tracially functorial exactification, support, polar, or block
operations, apply them in the left regular finite von Neumann algebra.
Cyclicity forces the positive carrier difference to have trace zero, and
faithfulness kills it.  This is
`universal-block-return-violates-the-regular-firewall`.  Therefore a
completeness-preserving proper-corner exception must authenticate its source
Gram by a genuinely finite-matrix coordinate operation.  This proves the
claimed scoped dichotomy without asserting that the open authentication
exists.
