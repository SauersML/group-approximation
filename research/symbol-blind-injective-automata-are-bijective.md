---
rg: 2
id: symbol-blind-injective-automata-are-bijective
kind: claim
title: A symbol-blind automaton that is injective at every alphabet size is bijective at every alphabet size, over every group
distinct_from:
  symbol-blind-automata-reduce-to-defect-counting: that proves the partition criterion and the equivalence with defect-counting identities, plus orders 0 and 1; this is the unconditional conclusion, still open.
  gottschalk-surjunctivity-conjecture: that covers every automaton at one fixed alphabet; this covers only alphabet-permutation-equivariant rules, and assumes injectivity at every alphabet size.
---

Let G be any group and M a finite subset of G containing e. Let sigma choose
one class of each set partition of M, and let tau_q(x)(g) = x(g sigma(pi_g x))
on [q]^G, where pi_g x is the partition of M by equality of x(gm).

**Claim (open).** If tau_q is injective for every q >= 1, then tau_q is
surjective for every q.

Every symbol-blind automaton at an alphabet of size at least |M|+2 has this
form (symbol-blind-automata-reduce-to-defect-counting, part 1).

The claim is a consequence of gottschalk-surjunctivity-conjecture. By
symbol-blind-automata-reduce-to-defect-counting it is equivalent to
symbol-blind-defect-counting-identities, a family of finite counting
identities of which orders 0 and 1 are proved. A counterexample over some
group would be a surjunctivity counterexample with no symbol-level structure
at all: the rule only reads the equality pattern of its window.

## Attempts

- **Pointed memory: settled**, from injectivity at a single
  q >= |M|+|M^{-1}M|, by
  symbol-blind-automata-on-pointed-memory-are-permutive.
- **Amenable groups: known.** The claim holds over amenable groups by the
  Garden of Eden theorem. The open case is non-pointed memory over a
  non-amenable group, such as {e,a,b,A} in F2.
- **Calibration over Z.** `pair_graph_over_z.py` decides injectivity at every
  q. On the memories {0,1,2}, {0,1,3}, {0,2,3}, {0,1,2,3}, {0,-1,1}, {0,-1,2}
  and {0,-1,1,2}, the identity is the only selector injective at every q.
  Symbol-blind rules injective at every q look rigid (translations). If that
  rigidity could be proved directly, it would settle the claim over every
  group. The F2 census has no exact decider yet: on {e,a,b,A} three selectors
  pass the finite-defect checks up to defect 3.
