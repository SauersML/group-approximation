---
rg: 2
id: pzk-tableau-private-s5-gauge-normal-form
kind: claim
title: The PZK tableau has private S5 gauge rows but only trace-level balance
artifacts:
  - research/artifacts/mastel-slofstra-tableau-compiler-audit-2026-08-23.md
distinct_from:
  mastel-slofstra-private-context-augmentation-preserves-defect: that proves a general weighted-algebra soundness statement for private context variables; this identifies the exact variables, clause menu, and canonical marginal profile of the later PZK tableau.
  smooth-label-cover-edges-are-finite-phase-projective-color: that classifies each smooth-label edge acceptance relation; this classifies the internal randomizing-tableau syntax and its surviving shared-bit overlap.
  bisynchronous-to-monomial-game-algebra-compiler: that asks for a full universal-algebra matrix-pair encoding; this supplies only a narrower source normal form and one chosen trace profile.
---

**ESTABLISHED STRUCTURAL NORMAL FORM.**  In

```text
Tab_sub(Obl(B^3SAT)),
```

every tableau letter `T_i(p,q)` and randomizer `r_i(j,k)` is indexed by one
input context `i` and is private to that context.  The only variables shared
between different input contexts are the five Boolean shares `x(1),...,x(5)`
of source Boolean variables.

The nontrivial clause menu is

```text
T_i(1,q)=pi^(iq)_(x_q),
T_i(p+1,q)=r_i(p,q-1)^(-1) T_i(p,q) r_i(p,q),
product_q T_i(4,q)=sigma_i.                              (PTN1)
```

The last two families are reversible finite `S5` word equations.  The first
is only a Boolean-to-permutation lookup: the paper does not require its two
branch permutations to differ, and an arbitrary branch pair is not a group
homomorphism from `C_2`.  Trivial pair clauses complete the subdivision.

In the canonical simulated perfect correlation, every at-most-four exposed
Boolean shares are jointly fair, every randomizer is Haar-uniform on `S5`,
each row-one entry is balanced on its two instruction values, and each
individual entry in rows two through four is Haar-uniform.  These are exact
rational trace statements for that correlation.  They neither make every
clause-answer law uniform nor impose balance in the universal BCS algebra.
For instance, a first gauge-update clause permits any `S5` value in its
row-one coordinate, while the simulated trace supports that coordinate on
only the two program instructions.

Thus the tableau localizes all non-Boolean gauge syntax without solving the
shared-projection placement problem or supplying operator-level column sums.
