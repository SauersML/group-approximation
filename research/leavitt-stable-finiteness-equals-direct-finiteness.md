---
rg: 2
id: leavitt-stable-finiteness-equals-direct-finiteness
kind: claim
title: For the Leavitt unit group algebra stable finiteness and direct finiteness are the same statement
distinct_from:
  leavitt-group-algebra-not-stably-finite: that is the open matrix-level failure itself, an existence question about `A, B` in some `M_n`; this is an established equivalence between two questions and asserts neither of them.
  leavitt-unit-group-algebra-not-directly-finite: that is the open scalar failure, the Kaplansky question proper; this is the established statement that the scalar and matrix questions coincide for this one algebra, and it settles neither.
  stable-finiteness-reduces-to-prime-field: that reduces the coefficient field for every group at once, leaving the matrix size untouched; this reduces the matrix size for one group, leaving the field untouched, and the two reductions compose.
  leavitt-matrix-amplification-in-unit-group-algebra: that is the structural input — matrix algebras over `S` sit inside `S` as corners; this is the finiteness consequence extracted from it by padding and unitizing.
  leavitt-unit-group-nonsurjunctive: that is the open Gottschalk failure for the group, which consumes the matrix statement; this is the established equivalence between the matrix and scalar statements, and its effect on that node is only to say which of the two now has to be settled.
  leavitt-gl-equals-el-and-perfect-unit-group: that transports statements between matrix ranks *of the group* `GL_n(R)`, using the prefix-code self-similarity of `R`; this transports a finiteness failure between matrix ranks *over the group algebra* `M_n(F_2[R^x])`, one level up, and although both descend from self-similarity neither is an instance of the other.
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
---

For `S = F_2[G]`, `G = L_(F_2)(1,2)^x`:

    S is stably finite   <=>   S is directly finite.

Equivalently, if `B A = I_n != A B` for some `n` and some `A, B` in `M_n(S)`,
then there are already `a, b` in `S` with `b a = 1 != a b`.

## Why it is true here and not in general

Nothing about group algebras over a field is being claimed.  For an arbitrary
group the two properties are not known to be equivalent, which is exactly why
the char-zero theorem is quoted in the stronger stable form.  What is special
here is `leavitt-matrix-amplification-in-unit-group-algebra`: this particular
`S` contains `M_N(S)` as a corner for every `N = 2^k`, because the Leavitt
algebra's self-similarity puts a commuting pair — a scalar copy of `G` and a
constant `S_3` — inside the single group `G`.

Given that, the argument is padding and unitizing.  A failure in `M_n(S)`
survives padding to `M_N(S)` with an identity block, transports along the
injective `j_N` to `ba = E_N != ab` inside the corner `E_N S E_N`, and becomes
a scalar failure on adding the complementary idempotent: `a + (1 - E_N)` and
`b + (1 - E_N)` have all cross terms zero, so the reverse product is `1` and
the forward one is not.

## What it changes

Three things, and the third is the one that matters.

1. **No search needs to range over `n`.**  A machine search may fix `n = 1`.
2. **A proof of direct finiteness is automatically a proof of stable
   finiteness**, so the two targets need not be attacked separately from the
   positive side either.
3. **The negative Gottschalk and Kaplansky lanes collapse, but the positive
   problems do not.**  `stable-finiteness-failure-refutes-surjunctivity`
   consumes the matrix statement, and the present node turns every such matrix
   failure into a scalar direct-finiteness failure.  Hence for `R^x` any
   **linear** counterexample to Gottschalk coming from a group-ring one-sided
   inverse simultaneously refutes Kaplansky.  In the other direction,
   surjunctivity implies stable (hence direct) finiteness by
   Bradford--Fournier-Facio Corollary 3.25.  But direct/stable finiteness does
   not imply full surjunctivity: it controls linear/additive cellular automata,
   not arbitrary nonlinear finite-alphabet rules.

It follows that the sentence "Nothing in this graph reduces the matrix problem
to the scalar one" in `leavitt-group-algebra-not-stably-finite` is no longer
true, and that node has been corrected.

## What it does not change

It supplies no witness and no obstruction.  The surviving lanes —
`leavitt-corner-one-sided-lift-exists` and
`left-invertible-lift-of-s0-in-leavitt-group-algebra` — were already scalar
lanes, and this node neither helps nor hinders them.  Its whole effect is on
the shape of the question, not on its difficulty.
