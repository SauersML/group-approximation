---
rg: 2
id: fg-q-rings-have-no-matrix-representations
kind: claim
title: A finitely generated ring containing Q has no unital ring homomorphism into any matrix ring over a nonzero commutative ring
distinct_from:
  integral-form-algebras-have-no-fg-subring-containing-q: that bounds finitely generated subrings of M_n(A ⊗ K) with A free abelian; this bounds unital homomorphic images of a finitely generated ring in M_k(C) for an arbitrary nonzero commutative ring C.
  fg-subrings-of-integral-form-algebras-omit-q: that concerns subrings of algebras with finitely generated structure constants; this is a statement about representations, used to exclude groupoid rings with arbitrary coefficient functions.
artifacts:
  - research/artifacts/gq-referee-a-fg-q-rings-have-no-matrix-representations.md
---

**ESTABLISHED** by `fg-q-rings-have-no-matrix-representations-proof` (lane proof; referee gq-referee-a
PASS, proof-gap lens, `research/artifacts/gq-referee-a-fg-q-rings-have-no-matrix-representations.md`; elementary,
no novelty claimed).

## Statement

Let `R` be a finitely generated unital ring with a unital map `Q -> R`, let `C` be a nonzero commutative
ring and `k >= 1`. Then there is no unital ring homomorphism `R -> M_k(C)`.

## Consequences

- **Residually finite-dimensional rings.** A finitely generated ring containing `Q` has no nonzero unital
  representation on a finitely generated free module over a commutative ring.
- **Rings exhausted by locally matricial pieces.** If a ring `S` is a directed union of unital subrings, each of which
  admits a unital homomorphism into some `M_k(C)`, then no finitely generated unital subring of `S` contains
  `Q`. This is how `af-groupoid-rings-have-no-fg-subring-containing-q` is proved.
- **Remark (not used).** With Posner's theorem, a finitely generated ring containing `Q` has no nonzero
  PI homomorphic image, since a prime PI ring embeds in matrices over a field.
