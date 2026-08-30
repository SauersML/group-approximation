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

the image of `alpha` in `pi_5(U(M_2(D)))` is nonzero.

This remains open.  The associated rank-two projective module is nontrivial
before Z and trivial afterward, although its stable K0 class is already zero.
The disappearance after tensoring with `Z` is automatic by
`stw99-lxxvi-z-stabilization-kills-unstable-unitary-kernel`, so it is no
longer an input to the witness.
Pureness of `C(S^6) tensor D` is now automatic from Seth--Vilalta,
[Continuous functions over a pure C*-algebra](https://arxiv.org/abs/2602.14809),
since `D` is simple and pure; it is no longer an input to the witness.

## Attempts

Taking `D=C` retains the classical unstable bundle but fails the required
pureness.  Taking `D=Z` makes the continuous field Z-stable from the outset,
so it cannot distinguish the before and after Cu maps.

A natural nonnuclear test coefficient was `D=C*_r(F_2)`: it is simple, pure,
stably finite, and not Z-stable.  Its continuous `S^6` field is pure by the
2026 theorem just cited.  However, this candidate is now ruled out by
`stw99-lxxvi-free-group-cannot-be-s6-coefficient`: it contains a unital copy
of `Z`, which already kills `alpha` before stabilization.

There is a second, purely finite-dimensional exclusion.
`stw99-lxxvi-unital-matrix-subalgebra-kills-s6-class` proves that a unital
copy of any `M_k`, `k>=2`, already kills `alpha`.  The tensor-amplification
map lands in `U(2k)`, which is stable in degree five, and its stable image is
the `k`-fold block sum of the stably trivial class `alpha`.

The sole remaining construction problem is therefore to find a unital simple
separable pure `D`, necessarily containing neither a unital copy of `Z` nor
a unital matrix algebra of size at least two, for which

```text
alpha maps nontrivially into pi_5(U(M_2(D))).
```
