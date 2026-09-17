---
rg: 2
id: sparse-branched-covers-with-sofic-pi1-give-sofic-lattice
kind: claim
title: A nonpositively curved 2-complex group is sofic once it has branched covers of vanishing branching mass with sofic fundamental groups
distinct_from:
  titz-witzel-sparse-defect-needs-dense-generator-surgery: that forbids producing marked models by sparse edits of exact finite sheets; this builds models from branched covers that are never edits of exact sheets, and transfers soficity from their fundamental groups.
  titz-witzel-soficity-is-one-finite-csp: that reduces soficity to one finite approximate CSP; this replaces the CSP by a geometric object, a sparse branched cover, plus soficity of its own fundamental group.
  kazhdan-consistent-partial-models-round-to-finite-actions: that rounds consistent partial models to genuine finite actions; here the models are not required to be consistent, only their branch set is sparse, and consistency is supplied by covering uniqueness on the complement.
---

**ESTABLISHED** (proof: `sparse-branched-covers-sofic-pi1-reduction-proof`).

**Setting.**  `Y` is a finite connected piecewise Euclidean 2-complex with
finitely many shapes which is locally CAT(0) (every vertex link has angular
girth at least `2 pi`), `G = pi_1(Y)`, `Delta = Y~`.  A *finite branched
cover* `p: X -> Y` is a finite 2-complex `X` with a map `p` sending each
closed cell isometrically onto a closed cell, such that for every vertex `x`
the induced map `Lk(x) -> Lk(p x)` is a covering map of finite graphs with
`Lk(x)` connected, of degree `d_x`.  The branch set is `B = {x : d_x > 1}`.
Away from the vertices `p` is an honest covering of some degree `N`; its
*branching mass* is

```text
beta(X) = (1/N) * sum_{b in B} d_b .
```

**Theorem.**
1. (Sufficiency.)  If for every `eta > 0` there is a finite branched cover
   `X` of `Y` with `beta(X) < eta` and `pi_1(X)` sofic, then `G` is sofic.
2. (Necessity of sparse branching.)  If `G` is sofic, then there are finite
   branched covers `X_n` of `Y` with `beta(X_n) -> 0`.
3. (Curvature is free.)  Every finite branched cover of `Y` is locally
   CAT(0), so `pi_1(X)` is a torsion-free CAT(0) group acting freely and
   cocompactly on `X~`.

So soficity of `G` is squeezed between two geometric statements.  The
necessary one is sparse branched covers.  The sufficient one is sparse
branched covers whose fundamental groups are sofic.  Residual finiteness of
the `pi_1(X)` is enough for the second.  The difference lies entirely in the
fundamental groups of the covers, which are CAT(0) groups of a much more
flexible kind than `G`.  They are not simple, have no property (T) in
general, and by `flat-hitting-branched-covers-have-hyperbolic-pi1` they can
be forced to be hyperbolic.

The proof uses only covering theory, Cartan--Hadamard, and the unique
lifting of the `r`-balls about vertices at distance at least `r` from `B`.
No ball-rigidity or label-recovery computation is needed.

DERIVATION
sparse-branched-covers-sofic-pi1-reduction-proof
