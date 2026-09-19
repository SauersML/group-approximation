---
rg: 2
id: deligne-triple-cover-central-generator-is-mf-radical
kind: claim
title: The central generator of Deligne's triple cover belongs to its MF radical
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
distinct_from:
  deligne-triple-cover-fd-central-invisibility: that proves z is killed by exact finite-dimensional representations; MF-radical membership requires z to be killed by every representation into a norm-matrix corona.
  deligne-central-mark-hs-collapse: that kills z in normalized Hilbert-Schmidt norm in all presentation microstates; this asks for operator-norm vanishing in every corona representation.
---

For a generator `z` of the central `C_3` in

```text
1 -> C_3 -> E_3 -> Sp_4(Z) -> 1,
```

one has

```text
z in Rad_MF(E_3).                                      (DMR1)
```

Equivalently, every homomorphism from `E_3` to a positive-natural-dimension
norm-matrix corona sends `z` to the identity.

## Attempts

- The established claim `deligne-triple-cover-fd-central-invisibility`
  proves the assertion only for constant finite-dimensional targets.  The
  missing passage from exact representations to asymptotic operator-norm
  representations is precisely the unresolved step.
- Since `Res_fin(E_3)=C_3`, this claim is equivalent to
  `deligne-triple-cover-is-not-mf`; the two reductions are recorded as Cairn
  routes so neither statement is advertised as an unconditional theorem.
- Point-norm stability at `z` would finish the claim by
  `fd-mark-stability-forces-mf-invisibility`, but no proof of that hypothesis
  for this cover is currently available.
