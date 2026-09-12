---
rg: 2
id: explicit-zpc-irs-gap-game-witness
kind: claim
title: Name and certify one concrete tailored game with perfect ZPC-IRS value and quantum value below one half
artifacts:
  - research/artifacts/zpc-perfect-decoding-gap-audit-2026-08-18.md
  - research/artifacts/perfect-zpc-irs-gap-2026-08-18.md
---

Produce a fully specified finite tailored game `G_0` together with a checkable
certificate that

```text
omega_ZIRS(G_0)=1,
omega*(G_0)<1/2,
```

and an actual perfect ZPC-IRS strategy witnessing the first equality.

**ESTABLISHED (2026-09-12)** by `explicit-zpc-gap-witness-by-recursion-theorem`.
There `G_0` is the TailoredMIP instance of a machine that searches the ZPC-IRS
upper hierarchy of its own game and halts when a bound drops below one. By the
recursion theorem that machine never halts, so both values follow. Scope:
- the "certificate" is that recursion-theorem proof. No finite LP certificate
  of `omega_ZIRS(G_0)=1` is claimed;
- the perfect strategy exists by compactness and is not described.
The downstream compiler routes use only the named game and the existence of
the strategy.

`perfect-zpc-irs-quantum-gap-game` proves existence of some such finite game by
an undecidability/hierarchy argument, but that argument does not identify which
instance realizes the perfect ZPC-IRS side.  Cairn's primary goal asks to
**exhibit** an explicit nonhyperlinear group, so a root route through this game
must eventually freeze a concrete source instance rather than use bare
existence.

## Attempts

- Make the hierarchy-separation proof effective on a fixed, explicitly chosen
  nonhalting machine rather than argue that some nonhalting instance must have
  ZPC-IRS value one. This was first recorded as needing a direct
  construction/certificate of the perfect ZPC-IRS strategy. That turned out to
  be unnecessary: the self-referential diagonal fixes the instance without
  exhibiting a strategy.
- Search the explicit TailoredMIP construction for a syntactic subclass of
  verifier instances whose ZPC-IRS perfect strategy is canonical (for example,
  an IRS strategy coming from an explicit non-cohyperlinear subgroup process),
  while the quantum soundness theorem still gives the constant gap.
- If the exact-support LCS lane produces an explicit group first, this node can
  remain an independent explicitness problem rather than blocking the program.
