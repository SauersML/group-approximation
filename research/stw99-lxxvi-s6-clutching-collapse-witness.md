---
rg: 2
id: stw99-lxxvi-s6-clutching-collapse-witness
kind: claim
title: A simple pure coefficient preserves an unstable S6 clutching class until Z-stabilization
artifacts:
  - research/artifacts/stw99-lxxvi-third-depth-audit-2026-08-30.md
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

There exists a unital separable simple pure C*-algebra `D` such that, for the
nonzero unstable clutching class

```text
alpha in pi_5(U(2)) = Z/2,
```

the following hold:

1. the image of `alpha` in `pi_5(U(M_2(D)))` is nonzero; and
2. its image in `pi_5(U(M_2(D tensor Z)))` is zero.

This remains open.  The associated rank-two projective module is nontrivial
before Z and trivial afterward, although its stable K0 class is already zero.
Pureness of `C(S^6) tensor D` is now automatic from Seth--Vilalta,
[Continuous functions over a pure C*-algebra](https://arxiv.org/abs/2602.14809),
since `D` is simple and pure; it is no longer an input to the witness.

## Attempts

Taking `D=C` retains the classical unstable bundle but fails the required
pureness.  Taking `D=Z` makes the continuous field Z-stable from the outset,
so it cannot distinguish the before and after Cu maps.

A natural nonnuclear test coefficient is `D=C*_r(F_2)`: it is simple, pure,
stably finite, and not Z-stable.  Its continuous `S^6` field is pure by the
2026 theorem just cited.  The sole unestablished input is the unstable
homotopy calculation for

```text
U(2) -> U(M_2(D)) -> U(M_2(D tensor Z)).
```

The recent selfless tensor theorem does not compute these unstable homotopy
maps.  Thus the route is now a single-input unstable-unitary problem.
