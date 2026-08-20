---
rg: 2
id: materialize-self-referential-zpc-game
kind: claim
title: Materialize the self-referential TailoredMIP fixed-point game as finite repository data
distinct_from:
  explicit-zpc-irs-gap-game-witness: That target asks for both a literal finite game and its value certificate; this node is only the finite-data extraction because self-referential-perfect-zpc-irs-gap already supplies the certificate.
---

Take the effective fixed-point index `e_*` from
`self-referential-perfect-zpc-irs-gap` and run the fixed
Bowen--Chapman--Vidick TailoredMIP compiler far enough to emit the complete
finite encoding of

```text
G_* = G_(e_*).
```

Commit a canonical machine-readable representation of its question sets,
variable sets, distribution, controlled-linear predicates, readable labels,
and ZPC edge structure, together with enough compiler provenance to check
that the data are exactly the output attached to `e_*`.

No new existence theorem is requested here.  The prerequisite theorem already
certifies

```text
omega_ZIRS(G_*)=1,
omega*(G_*)<1/2,
```

and attainment of the perfect ZPC-IRS value.  This node is the remaining
literal-explicitness step: replace the finite object specified by a terminating
compiler computation with the finite object written out and auditably frozen
in the repository.

## Attempts

- The mathematical search for an unknown nonhalting source machine is no
  longer needed: Kleene self-reference supplies one effectively.  The live
  task is to extract the concrete fixed-point index under an explicit machine
  numbering and then execute/transcribe the TailoredMIP compiler.
- If the paper implementation is not available as executable code, formalize
  only the deterministic syntactic compiler stages needed to expand this one
  fixed input; a general-purpose verifier implementation is unnecessary.
