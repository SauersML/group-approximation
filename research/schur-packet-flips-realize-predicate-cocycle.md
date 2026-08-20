---
rg: 2
id: schur-packet-flips-realize-predicate-cocycle
kind: claim
title: Two commuting packet flips have projective commutator equal to the predicate
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  schur-packet-child-square-is-pauli-transverse: that identifies the two intermediate subgroup commutants as transverse MASAs; this constructs two explicit commuting automorphisms of the full finite packet whose implementer cocycle detects exactly the forbidden sectors.
  commuting-automorphism-cocycle-forces-multiplicity: that derives divisibility from any supplied projective automorphism square; this supplies such a square canonically from every Schur predicate packet.
  controlled-central-phase-finite-group-barrier: that blocks a nonlinear central phase law inside one finite overgroup; this uses commuting stable letters for packet automorphisms, allowing their external multiplicity action to cancel the projective packet cocycle.
---

For the Schur packet `B_f`, define automorphisms

```text
alpha_P(p_(N+1))=J p_(N+1),       alpha_P fixes all other generators,
alpha_Q(q_(N+1))=J q_(N+1),       alpha_Q fixes all other generators. (SPF1)
```

They are commuting involutive automorphisms of the finite group `B_f` and
fix `A_f` pointwise.  On a forbidden selector sector `x`, every `B_f`-simple
`T_(x,lambda)` is invariant under both automorphisms.  With the corrected
relative Pauli pair `P_x,Q_x` of `(SCP4)`, implementers may be chosen as

```text
U_(alpha_P)=Q_x,                   U_(alpha_Q)=P_x,                (SPF2)
```

and therefore

```text
U_(alpha_P) U_(alpha_Q)=-U_(alpha_Q) U_(alpha_P).                 (SPF3)
```

On an allowed sector, the relative algebra is `C[C_2 x C_2]`; the two
automorphisms independently flip the two character labels and act linearly
and commuting on their four-element orbit sum.

Consequently, in the finitely presented HNN square

```text
<B_f,u,v |
 u b u^(-1)=alpha_P(b), v b v^(-1)=alpha_Q(b), [u,v]=1>,          (SPF4)
```

the external multiplicity of every invariant forbidden `B_f`-simple is even.
This is an explicit, entirely group-native predicate holonomy cell.  It
avoids the nonlinear controlled-phase groupification barrier: the phase is a
projective cocycle on the packet factor and is canceled, when possible, by
the external multiplicity factor.

One copy of `(SPF4)` is not a normalized-HS obstruction, since parity can be
repaired on one copy inside a large multiplicity.  A recurrent compressor
must generate independent copies whose binary cocycle rank grows beyond the
current multiplicity capacity or occupies a positive density of bounded
multiplicity fibers.

