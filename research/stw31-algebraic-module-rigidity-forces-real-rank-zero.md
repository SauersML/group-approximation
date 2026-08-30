---
rg: 2
id: stw31-algebraic-module-rigidity-forces-real-rank-zero
kind: claim
title: Closure-of-compacts Hilbert-module rigidity upgrades algebraic Cu to real rank zero
distinct_from:
  stw99-problem-xxxi-cu-algebraic-rr0: this is a conditional theorem and a counterexample certificate; it does not prove that every simple stably finite algebra has the required module rigidity.
artifacts:
  - research/artifacts/stw31-module-rigidity-frontier-audit-2026-08-30.md
---

# Closure-of-compacts Hilbert-module rigidity upgrades algebraic Cu to real rank zero

Call a separable stably finite C*-algebra `A`
**projection-exhausted closure-rigid** if countably generated Hilbert
`A`-modules `E,F` are isomorphic whenever

```text
[E]=[F]=sup_n c_n,
K(F) has a projection approximate identity,
```

for an increasing sequence of compact elements `c_n` of `Cu(A)`. This is
an asymmetric formulation: it asks for CEI equivalence to be isomorphism
when one module is already exhausted by projective stages. The nested model
constructed below shows that, on the closure of compact elements, this is
equivalent to the symmetric Brown--Ciuperca formulation; its advantage is
that it exposes the exact shape a counterexample must have.

## Theorem

If `A` is separable and stably finite, `Cu(A)` is algebraic, and `A` is
projection-exhausted closure-rigid, then `A` has real rank zero.

No stable-rank hypothesis occurs in the statement. Stable rank one is one
way to obtain the rigidity hypothesis, but the theorem isolates the
infinite-stage piece of the stable-rank-one argument that Problem XXXI
actually needs.

On classes of the form `sup_n c_n` with `c_n` compact, projection-exhausted
closure rigidity is equivalent to the symmetric Brown--Ciuperca rigidity
question. One direction is immediate. For the other, given arbitrary
`E_1,E_2` with that common class, construct the nested-projective model `F`
from the `c_n`. Then `K(F)` has a projection approximate identity, so the
one-sided property gives `E_1` isomorphic to `F` and `E_2` isomorphic to
`F`.

## Counterexample certificate

More sharply, suppose that `A` is separable and stably finite, `Cu(A)` is
algebraic, but `A` does not have real rank zero. Then there are
CEI-equivalent, nonisomorphic countably generated Hilbert modules `E,F`
such that

```text
[E]=[F]=sup_n c_n,       c_n compact and increasing,
K(F) has a projection approximate identity,
K(E) has no projection approximate identity.
```

One may take `E=closure(a ell^2(A))` for a strictly positive element of
a hereditary subalgebra of `A tensor K` witnessing failure of real rank
zero. For **every**
compact decomposition of `[E]`, a nested-projective model `F` obtained from
that decomposition has the displayed properties and cannot be isomorphic
to `E`.

Thus a counterexample to Problem XXXI cannot come from failure to realize
an individual compact class by a projection: stable finiteness already
rules that out. It must be an infinite-stage failure to identify a
hereditary module with the closure of its compact projective
approximants.

This also localizes what cancellation or hereditary `K_1` assumptions
would have to accomplish. At each finite stage the required module
isomorphism already exists. Any useful extra hypothesis must make those
finite-stage identifications coherent at the limit; projection
cancellation alone does not address that limit passage.

## Primary-source interface

Brown--Ciuperca, *Isomorphism of Hilbert modules over stably finite
C*-algebras*, arXiv:0811.0958, Corollaries 3.3--3.4, proves that compact
`Cu` classes over a stably finite algebra are represented by algebraically
finitely generated projective modules and that order between such a class
and another module is realized by compact containment. Their Question 5.1
asks for isomorphism of every pair in the closure of compact elements. The
hypothesis above is its equivalent projection-exhausted normal form. The
construction of suprema by nested Hilbert modules is from
Coward--Elliott--Ivanescu, *The Cuntz semigroup as an invariant for
C*-algebras*, arXiv:0705.0341.
