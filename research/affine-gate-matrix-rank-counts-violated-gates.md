---
rg: 2
id: affine-gate-matrix-rank-counts-violated-gates
kind: claim
title: A gatewise affine matrix compiler whose F2 rank equals the number of violated gates
artifacts:
  - research/artifacts/atomic-schreier-lamp-collapse-audit-2026-08-26.md
distinct_from:
  three-xor-violation-is-one-clifford-rank: that compiles one three-XOR equation and carries the class-two two-group packet that realizes its rank jump inside a group; this is the gate-by-gate circuit identity over F2, additive across all gates, with no packet attached and no sector selection claimed.
  boolean-predicate-is-one-rank-jump: that compiles an arbitrary truth table into a single rank jump through one algebraic branching program; this keeps every gate separate, so the total rank counts violations rather than reporting one bit.
  support-failure-has-fixed-pivot-rank-one-compiler: that detects a single nested-support atom at a fixed pivot; this reads a whole fan-in-two circuit and its entries stay affine in the wire bits.
---

Let `C` be a fan-in-two Boolean circuit with gates `g = 1,...,m`, and fix an
assignment of bits to every input and internal wire.  For a gate `g` let
`v_g in {0,1}` be its consistency-violation bit.  Then there are matrices
`R_g` over `F_2` whose entries are **affine-linear in the wire bits**, with

```text
rank_(F_2) R_g = 1 + v_g,                                        (AGR1)
rank_(F_2) (direct sum over g of R_g) = m + UNSAT_C.             (AGR2)
```

For an AND gate `z = x and y = xy` take

```text
R_and(x,y,z) = [ [1, x], [y, z] ],   det R_and = z + xy = v_g,
```

whose first row is never zero, so `(AGR1)` holds and every entry is affine even
though the gate is not.  For COPY, NOT and XOR the violation bit is itself
affine,

```text
v_copy = x + z,   v_not = 1 + x + z,   v_xor = x + y + z,
```

so `R_g = diag(1, v_g)` gives `(AGR1)` again.  `(AGR2)` is additivity of rank
over a direct sum.

A gap hypothesis `UNSAT_C >= alpha m` therefore becomes an extensive rank
surplus `alpha m` in one fixed compiled object, one unit of rank per unit of
computational inconsistency, rather than the one bit that compiling only the
output predicate returns.

## What this does not supply

`(AGR2)` is an identity about `F_2` matrices.  It carries no mechanism for
selecting the sector in which a group representation reads `v_g`, and the AND
violation bit `z + xy` is **not affine in the wire bits**.  So
`central-pinning-forbids-nonlinear-predicates` applies to it unchanged: a
central involution can pin only affine joint spectra on commuting involutions,
and the nonlinear sector always coexists with other irreducibles of the same
central character.  Turning `(AGR2)` into multiplicity requires exactly the
finite-dimension-specific selection mechanism that claim says is missing --
which is why the Taller--Vidick reduction is routed through 3-XOR with a noisy
long code, and why `three-xor-violation-is-one-clifford-rank` is stated for the
affine case only.

No route consumes this claim, deliberately: it is recorded as an established
identity with the obstruction that blocks its intended use stated beside it, so
that a later reader who rediscovers the gadget finds the block rather than the
promise.
