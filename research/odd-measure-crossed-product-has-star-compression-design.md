---
rg: 2
id: odd-measure-crossed-product-has-star-compression-design
kind: claim
title: The odd-measure crossed product carries a star compression design below the cylinder idempotent
distinct_from:
  odd-measure-crossed-product-unit-below-cylinder-idempotent: that asks for any b', c' with c' q_[0] b' = eps_-; this asks for the self-adjoint special case x* x = eps_- with q_[0] x = x, which is sufficient and is constrained by the weight theorem.
  star-compression-designs-need-weight-four-colliding-columns: that is the established set of necessary conditions on every star design; this is the open existence question.
artifacts:
  - research/artifacts/odd-measure-star-compression-designs-2026-09-12.md
---

**OPEN.** Exhibit `x in B = C(M_-, F_3) ⋊_alg V`, the signed Thompson crossed product, with

    x* x = eps_-     and     q_[0] x = x,

where `(f[g])* = (f o g)[g^-1]`. By Lemma 1.1 of the artifact, `b' = x` and `c' = x*` then solve
`odd-measure-crossed-product-unit-below-cylinder-idempotent`, hence the ternary corner, and refute
Gottschalk on `L_(F_3)(1,2)^x`. A star design is a finite certificate: all conditions are identities of
`F_3`-valued functions on the odd vectors of one finite clopen partition (artifact Section 5).

## Attempts

- **Honest and cancellation-free designs, dead.** `star-compression-designs-need-weight-four-colliding-columns`
  and `odd-measure-space-has-no-honest-thompson-compression`.
- **Two-term designs and difference-free memory sets, dead.** If the pairwise differences
  `g^-1 g'` of the memory set are all distinct, every off-identity component has one term, the
  coefficient supports are pairwise disjoint, and there are no collisions. Artifact Section 5.
- **Necessary shape.**
  * columns of weight at least four carry half the Haar mass;
  * colliding columns share at least two points with cancelling signs, equivalently the collision
    difference occurs for at least two pairs at the same base point;
  * the Thompson projection of the support is nonamenable (`odd-measure-corner-witnesses-need-nonamenable-thompson-support`).
- **Where it dies.** No weight-four orthogonal gadget with images inside `U_[0]` is known over any
  nonamenable subgroup of `V`. Periodic sliding windows over `Z` fail orthogonality at shift three.
