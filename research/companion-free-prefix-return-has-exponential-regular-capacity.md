---
rg: 2
id: companion-free-prefix-return-has-exponential-regular-capacity
kind: claim
title: Lossless algebraic return through independent positive prefixes has exponentially small regular capacity
distinct_from:
  exact-first-hit-ladder-kills-regular-carrier: That uses a positive-density exit at every level of one infinite ladder; this is a finite-depth obstruction requiring no exit estimate and applies directly to companion-free baseline return.
  full-pair-routing-of-complete-baseline-has-a-prefix-capacity-gap: That charges the negative companion created by a full index-two cell at one level; this rules out even companion-free typewise chart transport by the total capacity of the common positive prefix.
  finite-packet-functoriality-has-positive-regular-profile: That classifies stationary finite-packet type flows; this is the sharper exponential estimate forced by independent pulse signs.
---

**ESTABLISHED FINITE-DEPTH NO-GO.**  Let `Gamma` contain commuting
involutions `B_0,...,B_(N-1)` which generate `C_2^N`, and put

```text
C_n=product_(k<n)(1+B_k)/2.                            (CPR1)
```

Work in a matrix amplification of `L(Gamma)` with its normalized canonical
trace.  Suppose `Q_0,...,Q_N` are projections obtained functorially from
fixed group-algebra charts and

```text
Q_n<=C_n,                    tau(Q_n)>=tau(Q_0)         (CPR2)
```

for every `n<=N`.  Then

```text
tau(Q_0)<=2^(-N).                                      (CPR3)
```

Indeed `C_N` is the Reynolds projection of the embedded group `C_2^N`, so
its canonical trace is `2^(-N)`.  The last containment and persistence in
`(CPR2)` give the claim.  The same conclusion holds if `Q_n` is a finite
orthogonal sum of type projections transported by separate chart edges:
trace additivity proves persistence and the returned sum is still below
`C_n`.  It also covers taking a shared-variable reducing hull, since the
hull only increases the returned trace while remaining below the prefix.

Consequently a functorial companion-free baseline cannot feed the usual
finite first-hit contradiction.  If its exit fraction is `0<eta<=1`, then

```text
N eta tau(Q_0)<=N eta 2^(-N)<1.                        (CPR4)
```

This covers the natural proposed compilers:

- A typewise full-chart HNN edge maps each source central idempotent to the
  corresponding target central idempotent and preserves its trace.  If all
  returned target types are put under the common positive prefix, their sum
  satisfies `(CPR2)`.
- Adding a central auxiliary source sign and mapping its positive character
  to `B_n=+1` only moves the unused negative character outside the selected
  source type.  After the selected types are recombined, their total returned
  projection is still below `C_n`, so `(CPR3)` is unchanged.
- Splitting a baseline type into paired source halves and sending the halves
  to orthogonally tagged targets also leaves the sum of their traces
  unchanged.  Orthogonality makes the returned sum a projection below
  `C_n`, again giving `(CPR3)`.
- Amalgamating the literal shared-variable chart affects neither canonical
  trace nor the prefix Reynolds projection.  Taking the common reducing hull
  only increases trace, so it still satisfies `(CPR2)` and cannot repair the
  capacity deficit.

At the finite-group representation-ring level the same calculation says
that the total Plancherel weight of all target types on which `n`
independent central pulse signs act trivially is at most `2^(-n)`.  An HNN
isomorphism merely permutes source and target irreducible types with their
Plancherel weights; auxiliary characters cannot create weight after the
typewise returns are summed.

The scope is important.  This does not rule out an incidence extracted only
in matrices and false in `L(Gamma)`.  It proves that the missing hybrid seam
cannot be an exact group-algebra containment, a full finite-chart HNN
transport, a central-character change of coordinates, or an orthogonal
paired-source recombination.  A successful common-prefix return must use a
genuinely finite-dimensional multiplicity selection at the step asserting
`Q_n<=C_n`, or abandon independent first-hit prefixes.
