---
rg: 2
id: stw12-periodic-factor-decomposable-actions-are-af-embeddable
kind: claim
title: An outer-periodic non-AF tensor factor preserves Brown's AF-embedding conclusion
distinct_from:
  brown-af-automorphism-crossed-product-equivalence: Brown requires the entire coefficient algebra to be AF; here only one tensor factor is AF and the other can be a non-AF real-rank-zero AH algebra.
  stw12-periodic-actions-over-af-embeddable-algebras: that theorem requires the full automorphism to have finite order in the outer automorphism group; here only the non-AF-factor automorphism is outer-periodic, while the arbitrary AF-factor automorphism can make the tensor-product automorphism outer-aperiodic.
artifacts:
  - research/artifacts/stw12-periodic-factor-decomposition-audit-2026-08-30.md
---

Let `B` be a unital separable AF algebra, let `C` be a unital separable
AF-embeddable C-star algebra, and take automorphisms

```text
beta in Aut(B),        gamma in Aut(C),        gamma^n=Ad(v)
```

for some `n>=1` and some unitary `v in C`.  Put

```text
D=(B tensor_min C) rtimes_(beta tensor gamma) Z.
```

Then the following are equivalent:

1. `D` is stably finite;
2. `B rtimes_beta Z` is stably finite;
3. `D` is AF-embeddable;
4. `D` is quasidiagonal.

Consequently, if `C` is a unital AH algebra of real rank zero, then Rordam's
AH embedding theorem verifies the standing AF-embeddability hypothesis,
`B tensor_min C` is again an AH algebra of real rank zero, and Problem XII
has a positive answer for the decomposable automorphism `beta tensor gamma`.
Neither `beta` nor the full tensor-product automorphism is required to have
finite order even in its outer automorphism group.
