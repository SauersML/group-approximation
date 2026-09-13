---
rg: 2
id: bcc-groups-have-k-exact-module-triples
kind: claim
title: If G satisfies Baum--Connes with coefficients then every module triple over G is K-exact, so a module K-defect forces a coefficient failure of G
distinct_from:
  split-quotients-give-exact-reduced-crossed-products: that gives C*-level exactness of specific module triples from splittings, finite quotients or co-amenable sections; this gives K-exactness of ALL module triples over any group that satisfies Baum--Connes with coefficients, with no splitting hypothesis.
  k-inexact-module-triple-refutes-trivial-coefficient-bc: that turns a module K-defect into a trivial-coefficient counterexample for the bigger groups; this identifies which base groups G can host a module K-defect at all, namely only those that already fail BC with coefficients.
  some-nonexact-group-has-a-k-inexact-module-triple: that is the open existence of a K-defect; this is the fence that restricts where it can live.
---

**ESTABLISHED** by `bcc-groups-have-k-exact-module-triples-proof`.

Setting of `k-inexact-module-triple-refutes-trivial-coefficient-bc`: `G` countable
discrete, `V` a countable `Z[G]`-module, `W <= V`, `X = V^`, `Z = W^perp`,
`U = X \ Z`.

**Theorem.** If `G` satisfies the Baum--Connes conjecture with coefficients
(`mu_(G,A)` is an isomorphism in both degrees for every separable `G`-C*-algebra
`A`), then for every module quotient the reduced crossed-product K-theory sequence

```text
K_j(C_0(U) ⋊_r G)  ->  K_j(C*_r(V ⋊ G))  ->  K_j(C*_r((V/W) ⋊ G))
```

is exact at the middle for both `j`. Equivalently the full six-term sequence of
the ideal `C_0(U) ⋊_r G` is exact.

**Contrapositive (the fence).** If some module triple over `G` has a middle K-defect
in degree `j`, then `mu_(G, C(X))` is not surjective or `mu_(G, C(Z))` is not
injective in degree `j`. So `G` itself already violates Baum--Connes with
coefficients (with commutative dual-module coefficients `C(V^)` or `C((V/W)^)`).

**Consequences for the open input
`some-nonexact-group-has-a-k-inexact-module-triple`.**
- A witness group must **fail** Baum--Connes with coefficients. Non-exactness is
  necessary (Kirchberg--Wassermann) but not sufficient.
- By `higson-kasparov-haagerup-satisfies-bcc`, every a-T-menable group satisfies
  BCC, and **non-exact a-T-menable groups exist** (Osajda). None of them can host
  a module K-defect. So the whole a-T-menable class -- the first place one would
  look for a non-exact host -- is ruled out.
- The witness is therefore a non-exact, non-a-T-menable group that violates
  Baum--Connes with commutative coefficients. Concretely: a Gromov monster of
  Higson--Lafforgue--Skandalis type, but with the coefficient failure carried by
  an **algebraic** (dual-module) coefficient algebra `C(V^)` rather than the HLS
  boundary coefficients. That is exactly the tension with
  `module-dual-actions-have-no-wandering-open-sets`: the HLS ghost lives on a
  proper open orbit, which a dual-module action never has.

**A C*-defect need not be a K-defect.** For a non-exact group some action is not
inner exact (else `G` would be exact); yet if `G` also satisfies BCC (e.g. Osajda's
non-exact a-T-menable groups), the K-theory of every such non-exact sequence is
still exact in the middle, by the same diagram chase applied to that action's
`0 -> C_0(U') ⋊_r G -> C(X') ⋊_r G -> C(Z') ⋊_r G -> 0`. So over these groups
C*-inexactness routinely occurs with **no** K-defect. This is the general answer
to the sub-question of `window-defect-forces-module-triple-inexactness`: its
C*-criterion is strictly weaker than a K-defect, and the gap is realized.

**Model test.** For amenable, a-T-menable, or exact `G` satisfying BCC the theorem
returns exactness, matching `split-quotients-give-exact-reduced-crossed-products`
where those also apply. It says nothing when BCC fails, as it must, since that is
the only regime where the module route can live.
