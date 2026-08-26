---
rg: 2
id: exact-hnn-word-stabilizes-character-without-normalizer
kind: route
title: Use an exact HNN or Bass-Serre word to stabilize one character atom without normalizing its packet
target: tailored-checks-to-common-marked-group-extensions
requires:
  - stabilizer-corrector-hermitianizes-zero-compression
  - finite-character-idempotents-have-exact-hnn-transport
---

**INVALIDATED EXACT-STABILIZER PROPOSAL.**  Let `q=e_(H,chi)` be the selected
one-dimensional finite-character idempotent.  Use subgroup HNN edges, or a
word in a finite Bass--Serre extension, to obtain one group word `s` with

```text
q s q=s q,                                                (EHS1)
```

but arrange that `s` does not normalize the whole selector packet.  Then
`s` would be the selected-projection stabilizer required by the
operator-level corrector without entering the packet-normalizer no-gos.

`finite-character-one-sided-stabilizer-is-its-normalizer` invalidates this
route whenever the base finite subgroup embeds, as it does in the ordinary
HNN/Bass--Serre constructions under discussion.  The exact Hecke norm of
`q s q` reaches the full source norm only when
`H=sHs^-1` and the transported character equals `chi`.  Thus `(EHS1)` already
forces `s q s^-1=q` and makes `s` a packet normalizer.  A surviving
construction must use a genuinely proper source-to-larger-target section,
an additive group-algebra corner unitary, or a finite-matrix-only decoded
return rather than an exact group-word stabilizer loop.
