---
rg: 2
id: triangle-defect-globalizes-to-a-bounded-label-list
kind: claim
title: A small affine orientation defect yields a dimension-free set of candidate labels hitting a constant fraction of heavy cosets
distinct_from:
  affine-orientation-triangle-defect-is-small: that is the analytic estimate which must produce a high-density set of concurrent pairs; this consumes that density statement and produces the global list, and it is a set-theoretic averaging lemma.
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
  - research/artifacts/approximation-cs-root-audit-2026-08-31.md
---

**ESTABLISHED.**  The exact statement needed by the globalization half is
elementary and stronger than previously recorded.

Let `B` be a nonempty finite set and let `C_b` be a nonempty set for every
`b in B`.  Suppose `S subset B x B` is a set of **star-certified pairs** such
that

```text
Pr_(b,c uniform in B) [(b,c) in S] >= 1 - eta,                 (TDG1)
```

and every `(b,c) in S` satisfies `C_b intersect C_c != empty`.  Then there is
`b_0 in B` for which

```text
Pr_(c uniform in B) [C_c intersect C_(b_0) != empty] >= 1-eta. (TDG2)
```

Consequently `Q=C_(b_0)` is a hitting set of size at most
`max_b |C_b|`.  For the affine-orientation application every `C_b` is an
affine pair, so

```text
|Q| = 2,       Pr_(c in B)[C_c intersect Q != empty] >= 1-eta.
```

Thus the desired constants are `L=2` and `gamma=1-eta`, independent of the
ambient dimension `k`.  If the analytic input is only stated for uniformly
random **distinct** ordered pairs, adjoining the diagonal gives instead

```text
gamma >= (1 + (|B|-1)(1-eta))/|B| >= 1-eta,
```

so the same constants work.

The proof is the degree averaging identity

```text
E_(b in B) Pr_(c in B)[(b,c) in S] = |S|/|B|^2 >= 1-eta.
```

Choose `b_0` whose inner probability is at least the average.  Each certified
pair then makes `C_c` meet `C_(b_0)`, proving (TDG2).

In the original geometric language, a concurrent triple

```text
C_b intersect C_c intersect C_(b+c) != empty
```

is in particular a star certificate for `(b,c)`.  No affine-plane
classification, cocycle correction, sunflower theorem, or regularity lemma
is needed after the analytic step has supplied such triples with high density
under the product-uniform measure on `B x B`.

**Scope.**  This closes only the conditional globalization implication.  It
does not show that noisy heavy cosets have small defect; that remains
`affine-orientation-triangle-defect-is-small`.  It also does not supply the
unwritten soundness reduction in `glue-lemma-implies-rich-2to1-hardness`.
