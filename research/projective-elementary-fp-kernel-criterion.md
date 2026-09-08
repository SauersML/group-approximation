---
rg: 2
id: projective-elementary-fp-kernel-criterion
kind: claim
title: Finite presentation of a projective elementary group still requires the Steinberg kernel and center to be finitely generated in the appropriate senses
artifacts:
  - research/artifacts/boone-higman-projective-finiteness-gate-2026-09-08.md
---

Let R be a finitely presented unital associative ring and n>=4. Put

    E = EL_n(R),
    P = E/Z(E),
    K = ker(St_n(R) -> E).

Then the following are equivalent:

1. P is finitely presented.
2. E is finitely presented and Z(E) is finitely generated as a group.
3. K is finitely normally generated in St_n(R), and Z(E) is finitely
   generated as a group.

The assertion makes no assumption that the unstable kernel K is central.
It does not replace finite normal generation of K by finite generation
as an abstract group, and it uses no assertion about stable K_2(R).

Thus passing from E to P can remove a central obstruction to simplicity,
but cannot remove failure of finite presentation of E. A candidate for
the open projective ring-host construction must meet both clauses of (3).

