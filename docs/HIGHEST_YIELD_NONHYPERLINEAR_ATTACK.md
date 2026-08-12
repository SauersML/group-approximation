# Highest-yield remaining attacks: finite-multiplicity reconstruction first

Date: 2026-08-12

## Revised decision

The active construction target should no longer be another deformation of the
fixed inner-aligned Leavitt atlas.  The signed group-algebra identity

\[
d_{11}\in \sum_z k[A_8]d_z+
\sum_{s,g}k[A_8](g-1)d_s
\]

holds over every field.  It eliminates, in one stroke, every fixed-fold
square-zero construction on every finite-dimensional module, including
indecomposable modules, arbitrary multiplicities, and off-diagonal couplings.
Changing the characteristic or module is therefore dead work.

The relative-perfectness audit has now exposed a different, genuinely
matrix-specific atlas route.  The boundary group has both a classical
amalgam branch and a distant exact Leavitt branch, so arbitrary tracial or
group-theoretic alignment is false.  But in a canonical matrix microstate the
regular finite chart has a finite multiplicity algebra, whereas the exact
Leavitt regular model has an infinite coset multiplicity algebra.  The
highest-yield immediate gate is therefore:

> Fourier-compress the fixed order-eight root Heisenberg subgroup, take the
> Pauli blocks of the already explicit raw compressor words, and determine
> whether the full atlas identities force a binary Leavitt family in the
> finite multiplicity algebra.

This is a fixed symbolic block calculation.  If it succeeds, the elementary
matrix trace floor gives a uniform atlas gap and proves the Leavitt group
nonhyperlinear.  If an exact finite model or a missing block identity refutes
it, the route can be killed quickly.  The exact theorem and falsification
gates are in
`ATLAS_RELATIVE_PERFECTNESS_AND_COEFFICIENT_ENDPOINT.md`.

The best independent fallback is:

> Start with one fixed finite synchronous BCS/CSP game which has a perfect
> commuting-operator strategy but a uniform gap for finite-dimensional
> strategies, and construct a bespoke finite LCS game preserving those two
> properties.

No efficient or uniform compiler is sought.  Only this one source algebra has
to be linearized.

## Exact target theorem

Fix a finite synchronous BCS game \(B_0\) satisfying

\[
\omega_{qc}(B_0)=1,
\qquad
\omega_{qa}(B_0)\le 1-\eta
\tag{HL1}
\]

for some \(\eta>0\).  The negative solution of Connes embedding/MIP*=RE
supplies a finite game separation.  Gate 1 below is to pass one such game
through the current BCS/CSP reductions and verify, in one finite
presentation, that synchronous or oracularizable perfect completeness and a
constant finite-dimensional soundness gap are retained.  Those ingredients
exist separately in the literature; their exact composition for our chosen
instance must not be assumed without replaying it.

Construct a finite binary linear constraint system \(L_0\) and constants
\(c,C>0\) with:

1. **exact completeness:** every perfect commuting strategy for \(B_0\)
   induces a perfect commuting strategy for \(L_0\);
2. **robust soundness:** a finite-dimensional strategy for \(L_0\) of defect
   \(\delta\) induces a finite-dimensional strategy for \(B_0\) of defect at
   most \(C\delta^c\).

Then

\[
\omega_{qc}(L_0)=1,
\qquad
\omega_{qa}(L_0)<1.
\tag{HL2}
\]

The solution group of \(L_0\) has its distinguished central involution
nontrivial in a commuting representation but trivial in every asymptotic
matrix representation.  The standard LCS solution-group correspondence then
produces a nonhyperlinear group.

## Why this target is narrower than the published open problem

Taller--Vidick prove RE-hardness for LCS games with completeness
\(1-\epsilon\), and explicitly note that \(\epsilon=0\) would imply a
nonhyperlinear group.  Their completeness loss comes from deliberately added
noise in the distorted long-code test.  They also explain two barriers to a
generic perfect-completeness compiler:

* an efficient classical compiler would imply \(P=NP\);
* not every BCS algebra admits a morphism into an LCS algebra.

Neither barrier rules out the target above.  It is nonuniform, may be enormous,
and concerns one specially chosen non-CE algebra.  We should therefore avoid
trying to repair the noisy long-code test and instead test direct algebraic
linearizability of this single instance.

## First decisive gates

### Gate 1: freeze a finite source presentation

Extract from a current synchronous BCS/CSP MIP*=RE reduction one explicit
finite source \(B_0\), together with the two replayable implications in
`(HL1)`.  Record its projection generators, partition-of-unity relations,
local commutation relations, and forbidden products.

### Gate 2: exact LCS-algebra embedding test

Attempt to encode each source projection by a word in involutions of a finite
solution group, with the source partition and forbidden-product relations
holding identically.  This is an exact finite word problem.  The first search
should allow auxiliary variables and equations freely; efficiency and size do
not matter.

Kill the route immediately if a representation-theoretic invariant of the
specific \(B_0\) rules out every such encoding.  The generic obstruction is
not enough.

### Gate 3: robust reverse decoding

For a candidate exact encoding, prove a normalized-HS decoding estimate from
near-perfect LCS strategies back to near-perfect \(B_0\) strategies.  Use:

* HS stability of projection and involution relations;
* local commutativity gadgets;
* Paddock's dimension-independent BCS strategy/approximate-representation
  correspondence;
* finite telescoping only.

This gate must be dimension independent.  No bounded-dimension scan is a
substitute.

### Gate 4: solution-group extraction

Once `(HL2)` is certified, write down the finite solution-group presentation
and verify the distinguished central involution is visible in the commuting
model and uniformly invisible in matrices.  This is the final
nonhyperlinearity proof.

## Resource allocation

Stop:

* large-\(k\) unitary optimization;
* new characteristics or finite-field modules;
* fixed-fold first-order, Jordan, or off-diagonal variants;
* natural-overgroup scans beyond the completed \(A_9/A_{10}\) audit;
* generic perfect-completeness long-code repair.

Prioritize the Leavitt atlas only at the finite-multiplicity reconstruction
gate: the order-eight Heisenberg Fourier corner, the two raw compressor
blocks, and the smallest boundary-plus-interior packet.  Do not resume blind
large-\(k\) optimization or first-order deformations.

Retain the one-instance perfect-linearization program as the independent
fallback.  It starts with a known finite non-CE separation, but its missing
perfect-completeness compiler is broader and currently less tied to a fixed
symbolic identity than the compressor-block gate.

## Probability assessment

These remain attacks on a famous open problem.  Neither endpoint is close to
proved.  The finite-multiplicity route has the best immediate falsifiability
because its next claim concerns fixed blocks of explicit words; the
one-instance linearization route has the stronger external source separation
but a less explicit missing compiler.
