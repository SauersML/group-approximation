---
rg: 2
id: mf-obstruction-gives-a-finite-c-killing-relation-set
kind: claim
title: The MF obstruction yields a finite kernel set whose vanishing in any finite quotient already kills the 3-cycle
distinct_from:
  binary-leavitt-hyperlinear-iff-24k-feasible: that builds the increasing computable families T_m exhausting ker q and characterizes hyperlinearity by their normalized-HS defect infima; this extracts one finite subset with no metric content at all, asserting only that killing it in a FINITE quotient forces the 3-cycle to die.
  binary-leavitt-all-ranks-full-mf-radical: that is the MF obstruction itself, a statement about corona homomorphisms of the unit group; this is its finite-quotient shadow, obtained by a compactness argument that turns a hypothetical sequence of finite quotients into one corona homomorphism.
  leavitt-24k-first-relation-has-exact-finite-model: that identifies one explicit kernel word and evaluates it; this asserts the existence of a finite set and identifies none of its words.
artifacts:
  - research/artifacts/leavitt-error-basis-normalizer-obstruction-2026-09-08.md
---

**ESTABLISHED.** Let `q : P = C_3 * C_2^3 -> H` be the surjection of
`binary-leavitt-units-generated-by-c3-and-c2-cubed`, with `c` the
3-cycle generator. There is a **finite** `T` contained in `ker q` such
that every homomorphism `theta : P -> Q` onto a finite group with
`theta(T) = 1` satisfies `theta(c) = 1`.

Otherwise, exhausting the countable kernel by finite sets and choosing
finite quotients that kill each of them but not `c` produces, through the
left regular representations, a homomorphism into the unitary group of a
norm matrix corona that kills `ker q`, so factors through `H`, and is
nontrivial because left translation by an order-three element is
fixed-point-free, giving `||lambda(theta_n(c)) - I||_op = sqrt 3`. Its
image is MF, contradicting `binary-leavitt-all-ranks-full-mf-radical`.

**This is an existence statement only.** It identifies no word of `T`
and gives no bound on word length, so every constant derived from it is
explicit only once a `T` is exhibited. Its role is to convert the
analytic MF obstruction into a purely finite-group statement usable
inside a single matrix block.

DERIVATION
finite-c-killing-relation-set-proof
