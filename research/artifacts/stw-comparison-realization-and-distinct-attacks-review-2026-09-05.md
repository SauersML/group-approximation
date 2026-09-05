# Review of comparison, realization, and two distinct operator-algebra attacks

Date: 5 September 2026. Internal mathematical review record. The research
graph records proof dependencies; its checks are not formal verification.

## Results and division of work

The root developed intrinsic Cu comparison from compact equality-stratum
bundles. Ohm developed contraction of stably null unitaries supported in
full positive hereditary subalgebras with enough orthogonal Cuntz copies.
Pascal developed the moving spectral-threshold argument for maximal
free-product commutators whenever a represented projection side has
nonzero finite rank. Aquinas developed full hereditary sandwiches for
real-rank-zero simple finite pure coefficient fields. These were distinct
constructions, followed by targeted review of their dependencies.

## Mathematical review

The root reviewed the soft-support contraction proof, including the
continuous-field stable-rank bound for arbitrary hereditary subalgebras,
the exact hereditary matrix image from Cuntz cutdowns, fullness of small
cutdowns, nonunital scalar-quotient correction, and the quasitrace
partition argument. Primary Ng--Sudo, Rørdam, and Blackadar--Handelman
inputs were checked. No projection-support assumption is introduced.

The root reviewed the finite-rank-side proof. Strong-star continuity
of every fixed free-product element under moving threshold evaluation
becomes norm continuity after finite-dimensional compression. The
compressed selfadjoint matrix changes from the identity to its negative,
so a zero eigenvalue forces commutator norm one. The original full
two-isometry range projection has no finite-rank-side representation;
the unrestricted defect-projection corollary does not remove that limit.

Ohm and Aquinas independently accepted the root's compact equality-strata
comparison proof, conditional on the earlier exact relative-embedding
theorem. The review checked support continuity using finiteness, closure
of cutoff equality loci, finite clopen splitting of the compact core,
and zero extension on locally compact bases.

For the full realization proof the root checked the neighborhood
projection construction against spectrum accumulating at the lower
cutoff, both endpoint bundle identifications, and the passage from
hereditary sandwiches to surjectivity and arbitrary bases. Ohm separately
checked finite antichain interpolation, comparable closed patch overlaps,
descending exact frame extensions, and preservation of compact bundles
in the weighted sum. The root checked the primary coefficient inputs:
APRT Theorem 3.5 supplies Riesz interpolation; APT Proposition 5.4.4
identifies the maximal proper predecessor under weak cancellation;
Propositions 7.3.16--7.3.18 identify soft predecessors and give internal
soft approximation. These hypotheses concern the simple coefficients,
not the generally higher-stable-rank section algebras.

## Scope

The new realization theorem proves that the actual first-factor map

    Cu(C0(X,D)) -> Cu(C0(X,D tensor Z))

is an isomorphism for every second-countable locally compact Hausdorff X
and every separable simple stably finite pure real-rank-zero D. It
handles arbitrary accumulating compact fiber strata. The finite-
dimensional comparison and sandwich construction precede the inverse-
limit argument, so no projection stratum is assumed to descend to a
finite approximation of the base.

General STW LXXVI, LVIII, and LXI remain open. The named-problem count
remains one internally reviewed full-solution manuscript for LIX;
these four new theorems are not four additional solved named problems.
No external verification or publication priority is asserted.

## Repository validation

Scoped staged whitespace checks pass. On MSI, Cairn `check --changed`
and `preview` both exited zero on the dependency closure of 47 claims
and 44 routes (91 nodes). The initial scoped check identified two
existing permanence dependencies absent from the remote validation
snapshot; including their existing claims and routes resolved the
scope error without changing the proofs. All four new claims are
established in the graph, while the general open roots remain open.

No local code execution or builds were used for this round. The short
remote checks terminated normally, with no remaining job from this batch.
