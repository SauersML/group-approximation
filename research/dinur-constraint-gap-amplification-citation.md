---
rg: 2
id: dinur-constraint-gap-amplification-citation
kind: route
title: Import Dinur's preprocessing, graph-powering, and composition proof of linear-size gap amplification
target: dinur-constraint-gap-amplification
requires: []
---

# Literature import: Dinur's main amplification theorem

The target is exactly Theorem 1.5 of Irit Dinur, *The PCP Theorem by Gap
Amplification*, J. ACM 54(3), Article 12 (2007), DOI
`10.1145/1236457.1236459`.  The full February 13, 2007 manuscript supplied for
this import was read on 2026-08-20; its bibliographic identity was checked
against the author's publication page and author-hosted PDF.

## Proof dependency audit

The paper constructs

```text
G' = (prep(G))^t composed_with P
```

and proves the target by three quantitative steps.

1. **Preprocessing (Lemma 1.7).**  Vertex-cloud replacement makes degree
   constant, after which null constraints from a fixed expander family and
   self-loops give a regular expanding constraint graph.  Size grows linearly
   and UNSAT falls by at most a fixed factor `beta_1 > 0`.
2. **Graph powering (Lemma 1.6).**  For a regular constraint graph with
   self-loops and a fixed spectral gap, length-`t` walks give

   ```text
   UNSAT(H^t) >= beta_2 * sqrt(t) * min(UNSAT(H), 1/t).
   ```

   The proof decodes an arbitrary powered assignment by popular opinion.
   A middle window of the walk hits violated source edges often enough; a
   first/second-moment estimate and expander mixing turn those hits into
   rejected powered constraints.
3. **Composition (Lemma 1.8).**  Encode large-alphabet symbols by a
   constant-rate, constant-distance binary code and apply the constant-alphabet
   assignment tester of Theorem 5.1 to every robustized edge constraint.
   Shared codeword variables enforce consistency.  This restores a universal
   finite alphabet, changes size only by a source-alphabet-dependent constant,
   and preserves at least a factor `beta_3 > 0` of UNSAT.

Choose the constant `t` large enough that
`beta_1 * beta_2 * beta_3 * sqrt(t) >= 2`, and put
`alpha = beta_2 * beta_3 / sqrt(t)`.  Chaining the three displayed bounds gives

```text
UNSAT(G') >= min(2 * UNSAT(G), alpha).
```

Every operation has a constant size multiplier once `Sigma` and `t` are
fixed, so their composite has the claimed linear blowup.  Each operation also
preserves perfect satisfiability, which proves the completeness clause.

## What is and is not imported

This route imports the finite classical constraint-graph theorem only.  The
paper's analogy with parallel repetition, its assignment-tester extension,
and its short-PCP/LTC consequences are not being promoted here as additional
claims.  In particular, no quantum, operator-algebraic, or group-relator
extension is inferred from the word "amplification."
