---
rg: 2
id: leavitt-one-compressor-join-is-proper-amalgam-quotient
kind: claim
title: The literal one-compressor Leavitt join is a proper quotient of its two amenable factors' amalgam
distinct_from:
  leavitt-first-mixed-amenable-face-relator: that identifies an explicit shortest kernel word in the base-face amalgam; this proves noninjectivity for the full one-compressor factor amalgam without assuming an intersection formula for their HNN envelopes.
  leavitt-one-compressor-defect-lies-in-amenable-subgroups: that proves the two factors are amenable and contain the same defect; this proves their natural amalgam cannot equal their literal join.
  openai-leavitt-unit-nonsofic: that proves the Leavitt unit group is nonsofic; this applies subgroup closure and amenable-amalgam permanence to a particular pushout map.
---

Let

```text
A = Lambda_(L_0),
B = Lambda_P,
C = A cap B,
J = <A,B> = <L,tau,c>.
```

Then the canonical map

```text
q:A *_C B -> J                                             (PAQ1)
```

is surjective and has nontrivial kernel.

Indeed `A` and `B` are elementary amenable by
`leavitt-one-compressor-defect-lies-in-amenable-subgroups`, and `C`, being a
subgroup of either, is amenable. Amalgams of sofic groups over amenable
subgroups are sofic, so `A *_C B` is sofic. On the other hand `J` contains
`L=EL_3(L_(F_2)(1,2))`, which is nonsofic by the established all-positive-rank
Leavitt theorem. If `(PAQ1)` were injective, `J` would be sofic, contradicting
subgroup closure of soficity.

This proves that the tempting amenable-amalgam description is false. The
explicit base-face word of `leavitt-first-mixed-amenable-face-relator` is the
first visible candidate kernel relation. Certifying that this same word is
reduced in the full factor amalgam would additionally require the presently
unrecorded intersection identity

```text
Lambda_(L_0) cap Lambda_P = Lambda_(L_0 cap P).
```

The proper-quotient conclusion does not depend on that identity.
