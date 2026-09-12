---
rg: 2
id: binary-leavitt-unit-group-is-simple
kind: claim
title: The binary Leavitt unit group is simple
distinct_from:
  binary-leavitt-elementary-group-is-simple: that proves simplicity of EL_n(L) for every n>=3; this transports it to the unit group itself through the three-leaf prefix code, which is the form the Kervaire--Laudenbach lane consumes.
  leavitt-gl-equals-el-and-perfect-unit-group: that identifies GL with EL and proves perfectness; this adds simplicity, which perfectness alone does not give.
---

`G = L_(F_2)(1,2)^x` is a nontrivial simple group (infinite and nonabelian).

The three-leaf complete prefix code `{0, 10, 11}` identifies `L` with
`M_3(L)` as a unital ring, so `G = GL_3(L)`; over the binary Leavitt algebra
`GL_3 = EL_3`, and `EL_3(L)` is simple.

## Why it is worth a node of its own

Several Kervaire--Laudenbach nodes written before
`binary-leavitt-elementary-group-is-simple` landed say that `R^x` is known to
be perfect but not simple: the (b)-paragraph of
`kl-simple-failure-leaves-only-the-cyclic-quotient`, the maximal-form
discussion on `leavitt-degree-kernel-normally-generated-by-one-word`, the
closing remark of `leavitt-kl-violation-via-total-cyclic-collapse`, and the
distinct-from rationale on `kl-cyclic-orbit-perfect-kernel`.  Those caveats
are now stale (2026-09-11).  Part (a) of the cyclic-quotient theorem applies
to `R^x` itself, so a Kervaire--Laudenbach failure over the Leavitt unit group
cannot kill one coefficient and spare the rest: it kills the whole group and
leaves exactly `C_|m|`.  The equivalence is recorded by the two routes
`leavitt-kl-violation-via-total-cyclic-collapse` and
`leavitt-kl-violation-forces-kernel-normal-generation`.

Simplicity also sharpens the radical bound of
`nonsingular-adjunction-preserves-approximation-radicals`: the hyperlinear
radical of `G` is a normal subgroup, hence `1` or `G`.
