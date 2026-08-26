---
rg: 2
id: balanced-cross-matrix-unit-actions-have-m3-morita-model
kind: claim
title: Balanced cross matrix units and their native actions retain a three-object Morita model
artifacts:
  - research/balanced-cross-matrix-unit-morita-model-proof.md
  - experiments/balanced_cross_matrix_unit_morita_escape.py
  - research/artifacts/balanced-cross-matrix-unit-morita-escape-msi-2026-08-26.md
distinct_from:
  degree-zero-leavitt-core-has-locally-finite-marked-models: that treats arbitrary balanced coefficients but no uncancelled native s_i or t_i occurrence; this adds both nonzero gauge degrees and their literal actions by the two cross matrix units.
  aggregate-morita-common-opposite-return-has-gl3-square-model: that stops with two private returned branches; this also retains the subsequently audited private-middle swap, all four cross coefficients, and both complementary partial Whiteheads, then adds their full left and right action on native arms.
  full-depth-one-leavitt-menu-has-finite-clifford-model: that already fences both literal inverse rows, the common range sum, and every depth-one Weyl mixed square in a larger abstract occurrence model; this gives the narrower rectangular coefficient model which explains exactly how the new balanced actions fail.
  leavitt-range-sum-fold-is-first-object-erasing-row: that identifies the first relation leaving the typed path language; this proves that the balanced cross-action extension still does not erase the distinction between the range unit and the common source unit.
---

**ESTABLISHED BALANCED-CROSS FENCE.**  Extend the private-middle-swap
cross-return menu, including its four literal cross coefficients and both
complementary partial Whiteheads, by the native matrix-unit actions of

```text
e_ij=s_i t_j,     i,j in {0,1},                         (BCM1)
```

including `e_01=s_0t_1` and `e_10=s_1t_0`.  Include every such action which
can be displayed as an ordinary non-opposite Steinberg commutator:

```text
e_ij s_k=delta_(j,k)s_i,
t_k e_ij=delta_(k,i)t_j.                                (BCM2)
```

In particular the proposed bridge contains

```text
e_01s_1=s_0,   t_0e_01=t_1,
e_10s_0=s_1,   t_1e_10=t_0.                             (BCM3)
```

This really mixes the two nonzero-degree branch packets.  Nevertheless the
entire bounded table has an exact finite marked model.

Let `A=M_3(F_2)` with matrix-unit coordinates `(0,1,star)`, and put

```text
q_i=E_(i,i),       e_ij=E_(i,j),
s_i=E_(i,star),    t_i=E_(star,i),
p=E_00+E_11,       h=E_(star,star).                     (BCM4)
```

Then `(BCM1)--(BCM3)` hold, as does the stronger full table `(BCM2)`, while

```text
s_it_j=e_ij,
t_is_j=delta_(i,j)h,
q_0+q_1=p,
p+h=1_A,
p != h.                                                 (BCM5)
```

Represent every displayed root occurrence by the corresponding elementary
transvection over `A`.  Represent the coefficient-`1` parent occurrences
`N=x_78(1)` and `D=x_87(1)` by the local range unit `p`, while the separate
middle-coordinate swap `H=w_(9,10)(1)` acts by the full unit `1_A`.  Since
these coefficient-`1` occurrences are not identified by the scoped menu,
all aggregate, common-opposite, private-middle-swap, complementary
partial-Whitehead, balanced cross-definition, and cross-action relations are
exact.  This gives a model
inside the finite group

```text
GL_7(M_3(F_2)) <= GL_21(F_2).                           (BCM6)
```

The marked child is `x_78(q_1)` with coefficient `E_11`, hence is nonidentity.
Its left regular representation is an exact finite-dimensional unitary model
with nonzero negative spectral mass.

The cross matrix units and their actions therefore fuse the two private
`GL_3` branch factors, but only inside the range corner `pAp~=M_2(F_2)`.
They do not
identify its unit `p` with the common source projection `h`.  The missing
object-erasing row is precisely the literal source-unit relation

```text
t_is_i=1,                                                (BCM7)
```

typed so that the same coefficient-`1` occurrence is already represented by
`p`.  In this rectangular model its left side is `h`, so `(BCM7)` is exactly
where this particular `M_3` escape stops.  This is not a claim that adding
the inverse row closes the global problem: the established complete
depth-one Clifford firewall includes it and still keeps the mark.  Adding
further balanced matrix-unit actions, their Weyl transports, or their
ordinary non-opposite commutator consequences does not close the `p` versus
`h` gap in the present occurrence table.  The next live candidate must be a
depth-changing asymmetric payload return or another relation leaving the
finite depth-one role/Clifford action.

This is a scoped occurrence-table countermodel, not a representation of the
full binary Leavitt Steinberg group.  It does not fence a genuine same-root
occurrence identification of `(BCM7)`, and it does not refute global Atomic
Morita Return.  No Property `(T)`, Kazhdan input, stability theorem, trace
hypothesis, literature theorem, or Lean compilation is used.

DERIVATION
balanced-cross-matrix-unit-morita-model-proof
