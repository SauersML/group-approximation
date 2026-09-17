---
rg: 2
id: thompson-f-full-c-star-algebra-has-llp
kind: claim
title: The full group C*-algebra of Thompson's group F has the local lifting property
distinct_from:
  sp2g-z-full-c-star-algebra-has-llp: that is LLP for residually finite Kazhdan lattices, fenced by Ioana--Spaas--Wiersma at SL_n(Z); this is LLP for a torsion-free Haagerup group with no free subgroups, where the F_2 x F_2 fences do not apply.
  non-rf-kazhdan-group-with-llp-full-c-star-algebra: that asks for LLP for a non-residually-finite Kazhdan group, where Kirchberg's rigidity theorem turns hyperlinearity plus LLP into residual finiteness; this asks it for F, where the second input must be the failure of the factorization property itself.
---

**OPEN.** `C*(F)` has Kirchberg's local lifting property.

**Consumer.** `thompson-f-not-hyperlinear-from-llp-and-no-factorization`. With LLP, every hyperlinear
trace on `C*(F)` is amenable (`llp-makes-hyperlinear-traces-amenable`). So nonhyperlinearity of `F`
becomes exactly `thompson-f-lacks-factorization-property`.

**Position.**
- **If `F` is amenable,** `C*(F)` is nuclear and has LLP. The route then fails at its other premise.
- **Self-similarity.** `F` contains `F x F`, and `F x F` contains `F`. If LLP passes to full algebras of
  subgroups, this claim is equivalent to LLP of `C*(F) (x)_max C*(F)`. That passage is the standard
  permanence, since `C*(H)` sits in `C*(G)` with a conditional expectation.
- **Fences.** `F` contains no free subgroup, so neither the Ioana--Spaas--Wiersma obstruction nor the
  `C*(F_2 x F_2)` question enters through subgroups.
- **Negation.** If this fails while `F` is hyperlinear without the factorization property, `F` is a
  Haagerup group whose full algebra fails LLP.

## Attempts

- **Group-level permanence** (lane swarm-0917-w5-pull2-non-1, 2026-09-17). This is circular unless `F` is
  amenable.
  - **Available tools.** The standard sources of LLP for full group algebras are:
    - nuclearity of amenable groups;
    - passage to subgroups;
    - full free products;
    - amalgams over finite groups.
  - **Why they fail.** Each operation lies among (O1)--(O5) of
    `thompson-f-in-permanence-closure-only-via-base-copy`, and those operations preserve F-freeness. So a
    certificate for `C*(F)` built from them needs a building block that contains a copy of `F`, and that
    block already needs this claim. Starting from amenable blocks it reaches `F` only if `F` is amenable,
    and then `C*(F)` is nuclear anyway.
  - **Where it dies.** At the first decomposition step: every splitting of `F`, including its ascending
    HNN structure, has a vertex group containing `F`.
  - **What remains.** A direct tensor-product proof that
    `C*(F) (x)_min B(H) = C*(F) (x)_max B(H)`, or a refutation through a three-dimensional hyperrigid
    witness (`llp-failure-has-three-dimensional-hyperrigid-witness`).
