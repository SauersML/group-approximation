---
rg: 2
id: stw59-lean-witness-simple-unital-not-k1-injective
kind: claim
title: A Lean-verified nontrivial simple unital C*-algebra that is not K1-injective (STW LIX)
distinct_from:
  stw59-simple-ah-non-k1-injective: that claim additionally asserts K1(A)=0 and v^2 in U0(A) (component order exactly two); the Lean development proves neither -- HasK1InjWitness only asks that v is not in U0(A) and diag(v,1) is in U0(M2(A)), and K1(A) is never computed. It also does not assert nuclearity or stable finiteness of A. This claim is the weaker, machine-checked statement; the two are independent routes to the same refutation of STW Problem LIX.
artifacts:
  - notes/lix-lane-reports/lix-lemma-two-lean-closure-2026-09-07.md
  - research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md
---

There is a nontrivial, unital, separable, simple C\*-algebra `A` (Lean:
`GroupApproximation.LIX.LIXLimit`, the inductive limit of the STW LIX tower)
and a unitary `v` of `A` such that `v` is not null-homotopic in `U(A)` but
`diag(v,1)` is null-homotopic in `U(M2(A))`; hence `A` is not `K1`-injective.
This exact conjunction -- separable, nontrivial, unital, simple, not
`K1`-injective -- is the type of the named, hypothesis-free theorem
`GroupApproximation.NinetyNineProblems.exists_separable_simple_unital_not_k1Inj`
(carrier for the "separable" clause; see below), so nothing here rests on an
unnamed composite. This refutes STW Problem LIX
(`stw99-problem-lix-simple-k1-injective`), the same conclusion as
`stw59-simple-ah-non-k1-injective`, by an independent route: proved in
Lean 4 / Mathlib, mechanically checked, rather than reviewed on paper.

`stw59-twisted-section-parity-counterexample-proof` establishes the sibling
claim over the **integers**: an odd mapping-torus Chern number against an even
one, via Kunneth and Newton's identity on the projective factors. The Lean
route instead works over **F2**: the same finite twisted tower, but the
topological obstruction is a mod-2 top Stiefel-Whitney/Chern class computed
from a Thom class and a local-homeomorphism degree argument at one transverse
zero, using a vendored singular-cohomology development
(`GroupApproximation/ThirdParty/HamSandwich/SphereOddDegree/AlgebraicTopology`)
rather than any integral or K-theoretic machinery. The two routes are
mathematically independent verifications of the same finite bundle
obstruction, not restatements of each other; see the route node for the exact
chain of declarations.

Simplicity and separability of `A` are proved unconditionally
(`LIX.lixLimit_isSimpleCStar`, `LIX.lixLimit_separableSpace`, both
`#audit_closed_axioms`-clean). The witness unitary's existence is proved from
one topological input, `LIX.LemmaTwoHolds` -- at every stage of the tower, a
rank-`(2+m)` and a rank-`(3+m)`-minus-one bundle over `S^5 x (a product of
complex projective spaces)` are not Murray-von Neumann equivalent as
continuous fields -- and that input is now itself a theorem with no remaining
hypothesis, `GroupApproximation.CharClass.lemmaTwoHolds`. Assembled with the
rest of the C\*-side chain this closes
`GroupApproximation.NinetyNineProblems.not_problemLIX : ¬ ProblemLIX` and the
sharper `exists_separable_simple_unital_not_k1Inj`
(`Manuscript/NinetyNineProblems/ProblemLIX.lean`), both unconditional and both
carrying `#audit_closed_axioms`, landed at commit `aa9ba0148` -- confirmed an
ancestor of `origin/main` as of fetch `77e050e10`. See the route node for the
exact chain and for a correction: an earlier internal declaration,
`GroupApproximation.CharClass.not_problemLIX`, was removed at that same
commit to fix an import cycle and no longer exists.

**What is not claimed here.** `K1(A)` is not computed (not zero, not any
other group); the order of `v` in `U(A)/U0(A)` is not computed (not shown to
be exactly two); nuclearity and stable finiteness of `A` are not asserted.
None of these is part of the answer to Problem LIX -- see the route document's
scope note -- and none is proved by the cited declarations.
