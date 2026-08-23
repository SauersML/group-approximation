---
rg: 2
id: lin-pzk-tableau-rational-qc-not-qa-correlation
kind: claim
title: Lin plus the PZK tableau gives an explicit rational qc-not-qa correlation
artifacts:
  - research/artifacts/mastel-slofstra-tableau-compiler-audit-2026-08-23.md
distinct_from:
  lin-explicit-synchronous-bell-gap-game: that gives an effective separated game but does not single out a rational perfect correlation; this applies the zero-knowledge tableau to make all two-question statistics finitely samplable.
  lin-explicit-fixed-bcs-gap-via-generic-conversion: that gives the fixed separated BCS; this identifies one explicit rational non-Connes-embeddable correlation on a structured transformation of it.
  pzk-tableau-private-s5-gauge-normal-form: that audits the tableau syntax and warns that its raw local laws are not all flat; this proves separation and then gives a separate finite answer-splitting refinement with flat marginals.
---

**ESTABLISHED RATIONAL SEPARATION.**  Effectively construct from the Lin loop
BCS the finite tableau game

```text
B_tab=Tab_sub(Obl(B_loop^3SAT)).
```

Its Mastel--Slofstra simulator table `p_tab` is an exactly rational
synchronous correlation satisfying

```text
p_tab in C_qc,                 p_tab notin C_qa.          (PTR1)
```

Every entry is obtained by finitely many uniform choices from `{+1,-1}` and
`S5`, followed by deterministic finite-group operations.  Perfect commuting
completeness extends the `B_loop` trace through those classical masks and
randomizers and realizes precisely this table.  If `p_tab` were quantum
approximable, its perfect synchronous tableau strategy would pull back under
Mastel--Slofstra soundness to quantum strategies for `B_loop` with value
tending to one, contradicting its fixed positive gap.

There is an effective finite answer-splitting refinement `p_flat` for which
every question has the same number `L` of answers and

```text
p_flat(a|x)=1/L              for every retained answer a. (PTR2)
```

Choose a common denominator `L` of the rational marginals and split old
answer `a` into `L p_tab(a|x)` copies.  Tensor the commuting realization with
finite classical partitions to realize the copies.  Forgetting the copy
index maps any refined strategy back to `B_tab`, so
`p_flat in C_qc \ C_qa` as well.

Both `(PTR1)` and `(PTR2)` concern one explicitly selected trace.  They do
not force all traces of the tableau or refined game algebra to be uniform,
and they do not supply group-algebra projections or a canonical-profile
decoder.
