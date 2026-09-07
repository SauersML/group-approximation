# Gottschalk surjunctivity: research checkpoint, 2026-09-07

The requested conclusion is that every injective cellular automaton on every
finite-alphabet group full shift is surjective. **This session has not proved
that conclusion.** A dependency graph accepting a route, a finite experiment,
and a Lean kernel accepting a theorem are different kinds of evidence.

## Current-source check

Checked on 2026-09-07:

* OpenAI, [*Ten Advances in Mathematics and Theoretical Computer Science*](https://cdn.openai.com/pdf/ten-proofs-oai.pdf), updated 2026-08-06,
  Chapter 3, printed pp. 79–80, announces a nonsofic binary Leavitt unit
  group but explicitly leaves that group's surjunctivity undecided.
  Nonsoficity therefore supplies neither a proof nor a disproof here.
* Bowen–Chapman, [arXiv:2511.06586](https://arxiv.org/abs/2511.06586),
  describes the general conjecture as open and separates the group question
  from the invariant-random-subgroup question. Its older statement that no
  nonsofic group is known must not replace the August 2026 status check.
* The [formal-conjectures issue #2152](https://github.com/google-deepmind/formal-conjectures/issues/2152)
  concerns formalizing the conjecture's statement. Closing that issue does
  not supply a proof of the conjecture.

These checks found no full proof to import. They are a dated reconnaissance
record, not a claim that the entire literature has been exhaustively audited.

## Repository and Cairn baseline

The checkout began at `abef08251f4ae98f14c4f3813154abc4567833ba` on `main`.
The existing integration consists of `bin/cairn`, the pinned upstream
implementation `tools/cairn.py`, canonical `research/*.md` nodes, and the
research-site workflow. No second compiler or replacement graph is needed.

The existing claim
`finite-pattern-orbit-closure-forces-surjunctivity` proves surjunctivity when
the two pullbacks preserve finitely many rational pattern orbits. Its proof
also gives the local decoder for every injective full-shift automaton.
`gottschalk-surjunctivity-fixed-two-generator-tester` is an exact reduction
to one group, not a proof of surjunctivity of that group. The Leavitt
nonsurjunctivity root remains a separate, unresolved negative direction.

The first shallow-checkout invocation could not resolve historical artifact
pins. Fetching repository history repairs this checkout prerequisite; it does
not justify changing the canonical citations or weakening their validation.

## Attack: quantify the observable defect

For an injective encoder `tau` and a local decoder `sigma` with
`sigma tau = id`, put `T=tau*`, `S=sigma*` on local observables modulo
constants. Then `TS=I`. The reverse defect is `E=I-ST`.

The candidate argument is to propagate a nonzero finite seed `theta=E|P_0`
through `theta,S theta,...,S^(n-1) theta` and recover each component with
`E T^i`. On finite pattern-orbit modules these are finite matrices over
group-algebra projectives. Faithful group von Neumann dimension might then
give a quantitative lower bound proportional to `n`.

The verification tasks are substantive: show that the seed is nonzero
modulo constants; fix the orientation of the pullbacks; justify bounded
extensions only between finite orbit modules; and recover the blocks before
taking Hilbert-space closures. Algebraic independence alone does not justify
additivity after completion, and flatness of the group von Neumann algebra
over the group algebra must not be assumed.

Even a correct lower bound would be a conditional surjunctivity criterion.
There is currently no universal upper bound to contradict it. In particular,
the reversible two-track XOR rule already in the repository has unbounded
observable growth. Before proposing any sublinear upper bound, its actual
Hilbert-module growth must be checked on that example.

At the initial checkpoint the quantitative statement was an argument under
review. The following records the subsequently completed argument.

## Completed mathematical progress

The [full proof](../research/artifacts/gottschalk-observable-growth-2026-09-07.md)
establishes an exact formula: the first `n` copies of the observable defect
have total von Neumann rank `n delta`, where `delta>0` precisely when the
encoder is nonsurjective. Two bounded factorizations through finite orbit
modules justify the equality after completion. In particular, sublinear
growth of the unsaturated observable span is sufficient for surjunctivity.

The same artifact computes the reversible XOR example exactly: `d_n=2n+3`
and `delta=0` for all `n>=0`. Its decoder is unique. This disproves the
universal sublinear upper bound that would have completed this particular
attack. Linear growth of observables cannot on its own separate a strict
encoder from a reversible rule. The general conjecture is still unresolved.

The new positive Cairn goal is `gottschalk-surjunctivity-conjecture`. Its
fixed-host route has an explicit open prerequisite. The quantitative
theorem and the reversible rank calculation have their own proof routes;
neither is linked as though it proved the general conjecture.

## Evidence and novelty boundaries

The full-history baseline `bin/cairn check --json` passed with no findings.
The companion exact Python replay checks the bicyclic identities through
index 11, all matrix-unit products with indices below 8, normal-form words
through length 8, and the Walsh orbit windows through depth 12. The stored
JSON reports the precise counts. The mathematical proof, rather than this
finite replay, supplies the statements for arbitrary `n` and `G`.
No Lean files were added and no Lean kernel verification is claimed.

Repository searches included `pattern observable growth`, `surjunctivity`,
and `wandering defect`, with the notes corpus enabled. External searches
included `surjunctivity sublinear`, `cellular automata von Neumann dimension`,
and the projective-observable and bicyclic-matrix-unit terminology. The
finite-trace tools and one-sided-inverse algebra are standard; the finite
closure theorem and qualitative XOR example were already present here.
The quantitative refinement is a result derived in this session, not a
certified claim of priority. These searches are not an exhaustive audit of
all papers, appendices, or released code.
