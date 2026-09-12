---
rg: 2
id: asymmetric-kaplansky-compiler-has-halting-witness
kind: claim
title: An asymmetric exact compiler yields a halting fixed point and a certified inverse identity
distinct_from:
  recursive-quine-route-to-kaplansky-is-closed: that considers a compiler whose HALT branch already promises a whole counterexample; this splits the identity and defect between opposite branches and extracts a halting fixed point with a finite identity certificate.
  exact-group-algebra-death-cannot-code-nonhalting: that excludes opposite truth values of the same equality; this uses two different products, whose inequivalence is precisely the sought algebraic obstruction.
---

Suppose a total computable compiler C sends a machine index i to a finite
presentation G_i and finite matrices A_i,B_i over F_p[G_i], for one fixed
prime p, such that

    i does not halt  => B_i A_i=I,                       (AKC1)
    i halts          => A_i B_i!=I.                      (AKC2)

Then one can effectively obtain an index j which DOES halt, together with
a finite certificate of B_j A_j=I. By (AKC2), A_j B_j!=I. Thus C would
construct a stable-finiteness counterexample over a finitely presented
group and a finite-field linear-surjunctivity counterexample.

The witness program waits for a proof of its own B_j A_j=I. This is a
different, terminating extraction from the program that waits for
A_j B_j=I, which yields a nonhalting fixed point.

This is a conditional extraction theorem. No compiler satisfying (AKC1)
and (AKC2) is constructed. The existence of such a compiler is equivalent
to the existence of a finitely presented counterexample of this type,
because a constant compiler supplies the converse. That existence
equivalence does not rule out a nonconstant computational construction;
it identifies where the unproved algebra is located.

Any implementation whose final inverse defect is a nonzero projective
induced from a finite subgroup is excluded by
`lifted-trace-detects-finite-subgroup-projectives`. Thus a finite-subgroup
boundary projector cannot supply the defect, even with arbitrary ambient
transitions.

Replacing one finite packet by a finite closed family of such projective
states does not provide recurrent amplification through direct-sum
copying identities: `finite-subgroup-copy-circuits-have-no-recurrent-branching`
forces every recurrent component to be a simple cycle. A compiler using
different kinds of verification maps is not covered by that restriction.
