---
rg: 2
id: stw95-strongly-purely-infinite-cellular-factor-proof
kind: route
title: Tensor the infinite cells and assemble them through the exact filtration
target: stw95-strongly-purely-infinite-cellular-factor-preserves-purity
requires:
  - ks-exact-tensor-preserves-strong-pure-infiniteness
  - pasnicu-rordam-ideal-property-collapses-pure-infiniteness
  - stw99-lxxvi-strong-pure-infiniteness-implies-cu-regularity
  - stw95-transfinite-exact-filtration-reduction
  - stw95-semisplit-successor-filtration-reduction
artifacts:
  - research/artifacts/stw95-strongly-purely-infinite-cellular-tensor-audit-2026-08-30.md
---

For the direct assertion, let `C` be exact and strongly purely infinite.
After swapping the tensor coordinates, apply
`ks-exact-tensor-preserves-strong-pure-infiniteness` with `C` as both the
exact factor and the strongly purely infinite factor.  It gives
`C tensor_min D` strongly purely infinite for arbitrary `D`.  When `C,D`
are separable, `stw99-lxxvi-strong-pure-infiniteness-implies-cu-regularity`
makes the product pure.  Notice that no exactness of `D` is used.

Now consider the cellular assertion.  Fix a successor stage and write

```text
L_alpha=I_(alpha+1)/I_alpha.
```

It is separable because `A` is separable.  By hypothesis it is strongly
purely infinite.  Since `B` is exact,
`ks-exact-tensor-preserves-strong-pure-infiniteness`
gives

```text
L_alpha tensor_min B
```

strongly purely infinite.  This product is separable, so
`stw99-lxxvi-strong-pure-infiniteness-implies-cu-regularity` makes it pure.
Concretely, its Cuntz comparison is ideal containment, every Cuntz class is
idempotent, and idempotence gives both almost unperforation and almost
divisibility.

Thus every local hypothesis in
`stw95-transfinite-exact-filtration-reduction` is verified.  Exactness of
`B` identifies the successor quotients of the tensor filtration as
`L_alpha tensor_min B`; extension permanence handles successors, Cu
continuity handles countable-cofinality limits, and separability forces
stabilization at uncountable-cofinality limits.  That theorem gives purity
of `A tensor_min B`.

Taking `B` to be the scalar algebra proves that `A` itself is pure.
Therefore, when the originally chosen exact algebra `B` is also pure, both
inputs satisfy the hypothesis of Problem XCV and their minimal tensor
product is pure.

For the complementary cellular assertion, assume instead that every
`L_alpha` is exact and strongly purely infinite and every successor
extension is cpc semisplit.  Swap tensor coordinates in the
Kirchberg--Sierakowski theorem: exactness and strong pure infiniteness now
both belong to `L_alpha`, so

```text
B tensor_min L_alpha
```

is strongly purely infinite, hence pure, for arbitrary separable `B`.
Apply `stw95-semisplit-successor-filtration-reduction` with filtered algebra
`A` and tensor factor `B`.  It gives `B tensor_min A`, and therefore
`A tensor_min B`, pure without exactness of `B`.

Finally, if a cell is only assumed purely infinite with the ideal property,
`pasnicu-rordam-ideal-property-collapses-pure-infiniteness` first makes it
strongly purely infinite.  For a separable purely infinite cell, the same
import identifies the ideal property with a compact-open basis for its
primitive ideal space, proving the topological formulation as well.  The
same conversion applies to the direct factor `C`.
