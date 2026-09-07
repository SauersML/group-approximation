---
rg: 2
id: asymmetric-kaplansky-halting-witness-proof
kind: route
title: Halt on the positive identity certificate and use nonhalting completeness to force termination
target: asymmetric-kaplansky-compiler-has-halting-witness
requires:
  - lifted-trace-detects-finite-subgroup-projectives
  - stable-finiteness-failure-refutes-surjunctivity
---

Equality of finite group-algebra expressions over a finitely presented
group is uniformly recursively enumerable. For each expression, enumerate
partitions of its finitely many word occurrences into blocks whose
coefficient sums vanish in F_p, and dovetail derivations proving the words
within each block equal in the presented group. A successful partition
certifies zero even if further blocks happen to coincide. Conversely the
actual equality classes give such a partition when the expression is zero.
Apply this entrywise to a matrix equality.

Kleene's recursion theorem gives a machine index j whose behavior is:

    compute C(j);
    enumerate certificates of B_j A_j=I;
    halt as soon as one is found.

If j did not halt, (AKC1) would assert B_j A_j=I. The certificate
enumerator would then eventually find a proof and halt, a contradiction.
Therefore j halts. Its trigger supplies a finite certificate of B_j A_j=I,
and (AKC2) supplies A_j B_j!=I. Running j while retaining its certificate
is a terminating extraction procedure whenever the compiler has the
stated properties. No computable a priori runtime bound is needed.
The finite-field matrix witness gives the asserted linear cellular
automaton by `stable-finiteness-failure-refutes-surjunctivity`.

The complementary fixed point waits for a certificate of A_j B_j=I.
It cannot halt because (AKC2) contradicts its trigger. Hence (AKC1)
gives B_j A_j=I, and absence of a reverse-identity certificate gives
A_j B_j!=I. This second fixed-point program itself does not terminate.

A fixed counterexample supplies a constant compiler satisfying both
clauses, proving the stated converse. The finite-subgroup exclusion
follows because I-A_j B_j is a nonzero idempotent with zero K_0 class,
whereas the lifted-trace theorem detects every nonzero induced
finite-subgroup projective and every nonzero finite sum of them.

No proof is supplied that the two compiler clauses can be implemented.
A simulation theorem about word equality or valid machine histories
alone does not establish either convolution assertion.
