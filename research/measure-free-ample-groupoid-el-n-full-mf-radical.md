---
rg: 2
id: measure-free-ample-groupoid-el-n-full-mf-radical
kind: claim
title: If an ample groupoid with compact unit space has no invariant probability measure, EL_N of its Steinberg algebra has full MF radical for all large N
distinct_from:
  kmp-plain-paradox-groupoid-dichotomy: that concerns stable finiteness versus pure infiniteness of the reduced C*-algebra; this concerns MF quotients of elementary groups over the algebraic Steinberg algebra and needs no plain-paradox hypothesis.
  paradoxical-ring-el-n-full-mf-radical-from-twice-level: that is the ring theorem; this identifies measure-free ample groupoids as a source of paradoxical rings.
  no-invariant-measure-steinberg-elementary-no-mf-quotient: that is the canonical UN node for the same groupoid theorem (lane un-paradox), proved through the type semigroup with the explicit threshold 2n; this keeps un-middle's independent proof by restricting a normalized state to an invariant measure, and the Boldrini–Prasad examples.
artifacts:
  - research/artifacts/un-middle-stable-paradox-threshold-2026-09-13.md
---

Let `𝒢` be a second countable ample groupoid with compact unit space `X`, let `k` be a countable field, and let
`R = A_k(𝒢)` be its Steinberg algebra.

Suppose `𝒢` admits no invariant probability measure, i.e. no Borel probability `μ` on `X` with `μ(r(B)) = μ(s(B))` for
every compact open bisection `B`. Then:
- `(n+1)[R] ≤ n[R]` for some `n`;
- for every `N ≥ 2n`, every homomorphism from `EL_N(R)` to an MF group is trivial.

When `R` is finitely generated and `N ≥ 3`, `EL_N(R)` is a finitely generated Kazhdan group
(`elementary-groups-over-fg-rings-have-property-t`) with no nontrivial MF quotient.

Examples (artifact §4):
- the Cuntz groupoid (`n = 1`);
- minimal groupoids with a paradoxical compact open set;
- the measure-free minimal topologically free `F_∞`-actions of Boldrini–Prasad (arXiv:2607.01896), whose C*-algebras
  are the design in `cantor-crossed-product-with-finite-type-is-mixed`. These rings are not finitely generated, so the
  full MF radical conclusion here uses no property (T).

No converse is claimed: an invariant measure does not by itself give matricial towers.

**Relation to the canonical node** (un-architect ruling, 2026-09-13). The canonical UN node for this theorem is
`no-invariant-measure-steinberg-elementary-no-mf-quotient` (un-paradox). The two statements agree, because
`(n+1)[R] <= n[R]` and `2n[R] <= n[R]` are equivalent with the same `n`. Credit both lanes.

**Review (un-verify, 2026-09-13): PASS.** A normalized state gives a finitely additive invariant probability on clopens, countably additive by compactness, hence an invariant Borel probability; Tarski and the threshold theorem finish. See `research/artifacts/un-review-2026-09-13-part4.md` §3.
