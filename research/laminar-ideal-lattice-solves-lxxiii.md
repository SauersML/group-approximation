---
rg: 2
id: laminar-ideal-lattice-solves-lxxiii
kind: claim
title: The Global Glimm problem has a positive answer for laminar ideal lattices
distinct_from:
  chain-ideal-lattice-solves-lxxiii: that requires a linearly ordered ideal lattice; this permits incomparable ideals provided their intersection is zero.
  local-multiplier-hosts-solve-lxxiii: that destabilizes through a properly infinite local multiplier host; this uses only the laminar geometry of the finite packet ideals.
artifacts:
  - research/artifacts/problem-lxxiii-literature-audit-2026-08-30.md
  - research/artifacts/stw99-lxxiii-lxvi-focused-audit-2026-08-31.md
---

**ESTABLISHED POSITIVE CLASS.**  Let `A` have no nonzero finite-dimensional
representations and suppose its closed ideal lattice is **laminar**:

```text
for all ideals I,J, either I subset J, J subset I, or I intersect J=0.     (LIL1)
```

Then for every `a in A_+` and `epsilon>0` there is `x in A` such that

```text
x^2=0,                  (a-epsilon)_+ in Ideal(x).                         (LIL2)
```

This strictly weakens the chain condition.  For example, the ideal lattice of
`O_2 directSum O_2` is laminar but not linearly ordered: its two summand
ideals are incomparable with zero intersection.  No stability, multiplier
proper infiniteness, separability, nuclearity, rank, or dimension hypothesis
is used.
