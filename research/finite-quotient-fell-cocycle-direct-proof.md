---
rg: 2
id: finite-quotient-fell-cocycle-direct-proof
kind: route
title: Conjugate quotient fibres by a section and retain the kernel-valued blocks
target: finite-quotient-fell-untwisting-leaves-kernel-cocycle
requires: []
artifacts:
  - research/artifacts/finite-quotient-fell-cocycle-proof.md
  - GroupApproximation/GroupTheory/FiniteQuotientFellCocycle.lean
---

Let `q:G -> Q` be surjective, fix a section `s:Q -> G`, and use the
left-regular convention

```text
lambda(x) delta_a = delta_(x a).
```

For `R_g=lambda(q(g)) tensor pi(g)` and
`T(delta_a tensor xi)=delta_a tensor pi(s(a)^(-1))xi`, unitarity gives

```text
T^*(delta_a tensor xi)=delta_a tensor pi(s(a))xi.
```

Applying the three operators in order gives

```text
T R_g T^*(delta_a tensor xi)
 = delta_(q(g)a) tensor
     pi(s(q(g)a)^(-1) g s(a))xi.
```

The element

```text
c(g,a)=s(q(g)a)^(-1) g s(a)
```

lies in `ker(q)`, since its image is
`(q(g)a)^(-1)q(g)a=1`.  Direct cancellation also gives

```text
c(gh,a)=c(g,q(h)a)c(h,a).
```

Thus the section-dependent basis change converts the actor into the quotient
permutation together with a `ker(q)`-valued block cocycle.  It is a pure
permutation on a block exactly when `pi(c(g,a))=1`; in particular all blocks
are pure when `pi` factors through `Q`.  Conversely, the transformation alone
does not discard `pi|ker(q)`: its values are precisely the residual blocks.

For a fixed finite test window the same calculation is stable for approximate
representations.  In any bi-invariant matrix metric, put
`x=s(q(g)a)^(-1)`, `y=g`, and `z=s(a)`.  Then

```text
d(u(x)u(y)u(z),u(xyz))
 <= d(u(x)u(y),u(xy)) + d(u(xy)u(z),u(xyz)).
```

Only the two displayed multiplication defects are used for each pair `(g,a)`.
A finite window therefore uses a finite union of test pairs, so all residual
block errors tend uniformly to zero whenever those finitely many defects do.
This quantitative statement is only perturbative: it neither makes the exact
kernel values amenable nor turns their represented blocks into permutations.

The Lean artifact proves the three algebraic identities independently of
finiteness or Hilbert-space structure: kernel membership, the cocycle law, and
the represented block-conjugation formula.  It also records the exact
pure-block equivalence and the factor-through-`Q` special case.
