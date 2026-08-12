# Highest-yield remaining attack: one-instance perfect linearization

Date: 2026-08-12

## Decision

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

The best remaining expected-value attack is instead:

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

Continue the Leavitt atlas only as a secondary benchmark for any new
dimension-independent gadget or decoding theorem.  Its exact data remain
valuable, but its surviving obstruction is now fully nonlinear and
CE-specific.

## Probability assessment

This is still an attack on a famous open problem.  It is not likely in an
ordinary-project sense.  Its advantage is comparative: it begins with a known
finite non-CE separation and leaves one finite compilation problem, whereas
the Leavitt route must both discover and certify the CE separation from
scratch.
