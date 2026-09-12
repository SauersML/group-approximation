---
rg: 2
id: lcs-compiler-goal-equivalence-proof
kind: route
title: A single non-CE perfect LCS gives a constant compiler, and a compiler gives a nonhyperlinear group
target: lcs-compiler-target-is-goal-equivalent
requires:
  - locally-affine-support-bcs-is-exactly-the-lcs-boundary
  - re-oriented-lcs-compiler-gives-nonhyperlinear-group
---

Three implications, each short.

1. **Nonhyperlinear group and non-CE perfect LCS.**  Statement 2 of
   `locally-affine-support-bcs-is-exactly-the-lcs-boundary` (a finite binary
   LCS with a perfect tracial state and no Connes-embeddable perfect state)
   is equivalent to statement 3 there (a finitely presented nonhyperlinear
   group).  This is the Paddock--Slofstra solution-group equivalence.

2. **Non-CE perfect LCS gives a compiler.**  Fix such an `L_*` and define
   `L_M = L_*` for every machine index.  The map is total and computable.
   - A perfect tracial state has a GNS representation of the solution group
     in which the marked central involution acts as `-I`, so `J != 1` in
     `Gamma_(L_*)`.  This is `(PC1)` for every `M`, halting or not.
   - For a finite game, quantum value one gives strategies with defect tending
     to zero and hence, along an ultrafilter, a perfect state on the synchronous
     algebra factoring through a matrix ultraproduct, i.e. a perfect
     Connes-embeddable state.  None exists, so `omega_q(L_*) < 1`.  This is
     `(PC2)` for every `M`.

3. **Compiler gives a nonhyperlinear group.**  This is
   `re-oriented-lcs-compiler-gives-nonhyperlinear-group`: the proof-search
   fixed point of Kleene's recursion theorem produces a nonhalting index whose
   solution group keeps `J != 1` while its quantum value is below one, and that
   group is nonhyperlinear.

Hence statements 1, 2 and 3 of `lcs-compiler-target-is-goal-equivalent` are
equivalent.  Implication 2 contains no decoder and no gap construction, which
is exactly why the compiler interface adds nothing to the goal.
