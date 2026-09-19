# STW XXXI closure-of-compacts module audit (2026-08-30)

## Result

The package proves a conditional extension of the known stable-rank-one
result and an unconditional necessary certificate for any counterexample.
It does **not** solve Problem XXXI.

## Checked inputs

1. **Compact realization needs no stable rank one.** Brown--Ciuperca,
   arXiv:0811.0958, Corollaries 3.3--3.4: over a stably finite algebra a
   compact `Cu` class is represented by an algebraically finitely generated
   projective Hilbert module; if it lies below another module class, it is
   represented by a compactly contained submodule there.
2. **Nested modules realize suprema.** The sequential-supremum construction
   is the Hilbert-module model in Coward--Elliott--Ivanescu,
   arXiv:0705.0341.
3. **Projection approximate identity.** A finitely generated projective
   stage is orthogonally complemented. Projections onto nested stages
   converge strongly on the dense union, hence form an approximate identity
   on compact endomorphisms.
4. **Real-rank-zero passage.** If the canonical module `H_a` is isomorphic
   to its nested-projective model, `Her(a)=K(H_a)` inherits that projection
   approximate identity. Doing this for every positive `a` gives the
   hereditary characterization of real rank zero.

## Exact frontier

The reduction puts Brown--Ciuperca Question 5.1 in an asymmetric normal
form: one of the two modules has a projection approximate identity in its
compact endomorphisms. This is not claimed to be logically weaker. Indeed,
the nested model shows equivalence with the symmetric question on the
closure of compact elements. Any XXXI counterexample is forced to refute it
in a very specific asymmetric way:
the same algebraic `Cu` class has one module whose compact endomorphisms are
projection-exhausted and one whose compact endomorphisms are not.

This rules out a common false route. Projection cancellation,
`K_1`-injectivity, or finite stable rank cannot be invoked merely to realize
the compact stages; those stages are already rigid by stable finiteness.
Such hypotheses matter only if they prove coherent infinite-stage module
isomorphism. No such implication is claimed here.

## Scope guard

The separability hypothesis is used to work with sequences and strictly
positive elements. Stable finiteness is used at compact-class realization.
Simplicity is unnecessary for the conditional theorem, though it remains
part of Problem XXXI.
