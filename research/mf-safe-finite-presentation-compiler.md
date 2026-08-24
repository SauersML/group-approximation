---
rg: 2
id: mf-safe-finite-presentation-compiler
kind: claim
title: Compile the FIN free-factor switch to finite presentations without losing its MF branch
distinct_from:
  threshold-free-reverse-kleene-mf-higman: that compiler preserves a marked radical/nontriviality dichotomy and yields one non-MF group; this must preserve an actual MF positive branch across every input.
  monotone-mf-switch-positive-branch-barrier: that rules out one append-on-halt marked architecture; this asks for a nonmonotone or MF-safe finite-presentation envelope.
  symmetric-double-weak-mf: that proves one MF-safe group operation; this needs a complete effective compiler assembled from such operations.
---

Construct a total computable map `e |-> P_e` into finite presentation codes
such that

```text
W_e infinite  => Carrier(P_e) is MF,
W_e finite    => E embeds in Carrier(P_e),
```

for one fixed finitely presented non-MF group `E`.

Generic effective Higman embedding does not solve this.  It preserves the
negative branch because the recursively presented switch embeds, but when the
switch group is trivial its finitely presented Higman ambient need not be MF.
The missing ingredient is an MF-safe replacement for the asymmetric HNN and
amalgamation machinery in the usual compiler.  Shulman's permanence for
symmetric doubles, central HNN extensions, and selected amenable amalgams
supplies promising building blocks but not this compiler.

## Attempts

The doubles/amenable-edge refactor stops at asymmetric HNN identification;
that missing gadget is now an explicit child claim.
