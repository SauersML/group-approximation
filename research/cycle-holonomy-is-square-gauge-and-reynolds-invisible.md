---
rg: 2
id: cycle-holonomy-is-square-gauge-and-reynolds-invisible
kind: claim
title: Balanced cycle holonomy is square-gauge and Reynolds-invisible
distinct_from:
  oracular-local-block-detectors-miss-balanced-cycle-holonomy: that proves local packet data leave arbitrary cycle monodromy; this tests two proposed approximation-specific readouts of that monodromy.
  central-square-orients-transverse-ledger: that positively orients a named raw lift already tied to a payload; this proves a square clause on a freely chosen transporter holonomy merely fixes its gauge.
  reynolds-rank-gap-forces-hs-holonomy-energy: that charges transport between Reynolds projections of different ranks; this proves an equal-type cycle monodromy fixes its Reynolds projection exactly.
---

**ESTABLISHED NO-GO for bare balanced transports.**  Let a connected finite
context graph carry copies of one exact finite packet representation and
equal-rank edge intertwiners.  Gauge along a spanning tree.  For each chord,
the fundamental cycle product is a unitary

```text
V in rho(F)' = I_packet tensor U(M).                    (CHR1)
```

When the edge relations are the bare unitary covariance equations (with the
reverse edge represented by the inverse), the chord intertwiner is a torsor
over this full commutant.  Multiplying that one chord on the source side by a
prescribed commutant unitary changes its fundamental monodromy to any
prescribed `Z in U(M)` and preserves every local intertwining/covariance
equation.  Different fundamental chords can be changed independently.  An
extra order or phase relation is already additional non-covariant incidence
and lies outside this bare case.

Consequently a fresh approximation-specific extension imposing

```text
V^2=J                                                     (CHR2)
```

does not reject a matrix transport type.  On the `J=+1` sector choose
`Z=I`; on `J=-1` choose `Z=iI`.  The extension has simply selected one point
of the transporter torsor.  The same choice is available in every finite
multiplicity and in the common properly infinite completion.

Adjoint Reynolds comparison is exactly blind to the same datum.  If

```text
R_F=|F|^(-1) sum_(f in F) Ad(rho(f)),                    (CHR3)
```

then every `V` in `(CHR1)` commutes with all represented packet words, so

```text
Ad(V) R_F Ad(V)^* = R_F.                                (CHR4)
```

Transporting the Reynolds projection around the entire cycle therefore has
zero superoperator defect for every monodromy.  A Reynolds rank payment can
detect a predicate-induced change of packet type or fixed-space dimension;
it cannot detect pure equal-type cycle placement.

There are only two ways a phase square can become nonvacuous.

1. Put the transporter names and hence `V` in the common base before issuing
   challenges.  Then `(CHR2)` is a genuine restriction, but types already
   satisfying it survive; mutually incompatible phase clauses on the same
   `V` cannot all share one exact completion.
2. Canonically tie a raw lift to a payload coefficient or selected proper
   corner, so commutant retuning changes a separately authenticated word.
   This is precisely the charged-section/nontransport return gate, not a bare
   transporter or Reynolds gadget.

Thus approximation-specific extension profiles still help when a base type
**does not admit** the requested transports.  Once it does, neither a free
square clause nor adjoint Reynolds comparison reads its residual monodromy.
The required cell must break the commutant torsor using payload-sensitive
incidence while remaining common-complete.

## Attempts

- A central square is genuinely phase-sensitive for a named payload lift,
  but a freely existential chord can always be rephased to satisfy it.
- Taking higher roots or several fresh phase gadgets has the same escape:
  each gadget chooses its own transporter unless the names are moved into the
  common base.
- Sharing transporter names makes the phase observable, but incompatible
  approximation-specific clauses then destroy common completeness.
- Reynolds averaging is stronger than scalar trace but is invariant under
  the entire multiplicity commutant, giving the exact zero in `(CHR4)`.
