---
rg: 2
id: stw95-cu-z-tensor-counterexample
kind: claim
title: Problem XCV's Cu(Z) tensor assertion fails by cross K1 becoming compact
artifacts:
  - GroupApproximation/Manuscript/NinetyNineProblems/ProblemXCVCompactKTheory.lean
  - research/artifacts/stw95-formalization-boundary-2026-08-30.md
---

The first assertion in Problem XCV of Schafhauser--Tikuisis--White has a
negative answer, even for separable unital simple **nuclear UCT,
Z-stable** algebras.  One explicit construction is the crossed product of
the bilateral tensor shift on `tensor_(j in Z) Z`; its certificate is
`stw95-bernoulli-z-crossed-product-counterexample-proof`.

Independently, the range theorem supplies such an algebra `E` with

```text
(K_0(E),K_0(E)_+,[1_E])=(Z,N_0,1),    K_1(E)=Z,
T(E)={tau}.
```

Then `Cu(E)=Cu(Z)`, but `K_0(E tensor_min E)=Z^2`, which forces
`Cu(E tensor_min E)!=Cu(Z)`.  The direct certificate is
`stw95-nuclear-range-cross-k1-counterexample-proof`.

There is also a concrete nonnuclear counterexample.  Put

```text
A = B = C*_r(F_2).
```

Then

```text
Cu(A) = Cu(B) = Cu(Z),       but       Cu(A tensor_min B) != Cu(Z).
```

This does **not** answer the more general permanence question: the tensor
product in this example is itself pure.  It only shows that pureness does not
prevent tensor products from acquiring new compact Cuntz classes.

The independent direct certificate is
`stw95-free-group-cross-k-theory-counterexample-proof`.  Its key point is
that a Cu-isomorphism preserves compact elements, while stable rank one
identifies their Grothendieck completion with `K_0`.  The Pimsner--Voiculescu
sequence gives `K_0(A tensor_min A) = Z^5`, whereas the compact branch of
`Cu(Z)` has Grothendieck completion `Z`.

## Scope and literature audit (2026-08-30)

* [Gong--Lin--Niu's range/classification theorem, Theorem 13.46](https://arxiv.org/abs/1501.00135)
  realizes the nuclear invariant used in the first certificate.
* [Strict comparison in reduced group C*-algebras, Theorem D](https://doi.org/10.1007/s00222-025-01366-5)
  gives the factor computation used above.
* [Ozawa, Proximality and selflessness for group C*-algebras, Theorem 2](https://arxiv.org/abs/2508.07938)
  proves tensor stability of selflessness for exact factors; its latest
  version is dated 2026-04-24.
* [Robert, Selfless C*-algebras, Theorem 3.1](https://arxiv.org/abs/2309.14188)
  supplies stable rank one in the tracial selfless case, and the
  [Pimsner--Voiculescu free-group exact sequence](https://jot.theta.ro/jot/archive/1982-008-001/index_1982-008-001.html)
  supplies the displayed `K_0` calculation.
* The post-April paper
  [Selfless C*-correspondences, operator valued C*-probability spaces and completely positive maps](https://arxiv.org/abs/2607.20361)
  extends tensor-product selflessness to further exact/simple uniquely
  tracial settings, but does not assert that arbitrary tensor products of pure
  C*-algebras are pure.
* An arXiv `math.OA` metadata scan from 2026-04-01 through 2026-08-30 for
  `pure`, `Cuntz`, `tensor`, `selfless`, `regularity`, and `comparison` found
  no explicit resolution of the general permanence question.  Thus the
  broader half of Problem XCV should remain marked open, not established or
  refuted by this node.

The nuclear range example proves that the obstruction is not a tensor-norm,
exactness, or nonnuclearity pathology.  It is invisible in either factor's
ordinary Cuntz semigroup because `K_1` is invisible there; the external
`K_1 x K_1` classes become compact `K_0` data after tensoring.
