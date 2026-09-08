---
rg: 2
id: cyclic-shift-finite-prefix-proof
kind: route
title: Extend a finite prescription by a finite perturbation of the zigzag and use countability for bad extensions
target: cyclic-shift-finite-prefix-cannot-decide-fp
requires: [zigzag-cyclic-shift-envelope-is-finitely-presented, shift-envelope-fp-enumerations-are-countable]
artifacts:
  - research/artifacts/boone-higman-zigzag-shift-compiler-2026-09-08.md
---

Suppose mu=sigma composed with nu for a finitary permutation sigma of N.
Extend sigma to a finitary permutation sigma_even of N by acting on the
even positions 2n->2sigma(n) and fixing odd positions. The regular P
images for mu and nu are conjugate by sigma_even. Since sigma_even
belongs to E_2, adjoining E_2 to either image gives exactly the same
subgroup E_mu(P)=E_nu(P). This proves finite-perturbation invariance.

Now let f be a finite injective partial map Z->N and nu_0 the zigzag
enumeration. The finite injective prescription nu_0(z)->f(z) extends to
a finitary permutation sigma of N: complete it to a permutation of the
finite union of its domain and range, and fix everything else.
Thus nu=sigma composed with nu_0 extends f, and its envelope is the
same finitely presented group as E_nu_0(Z).

On the other hand, continuum many bijections extend f, while only
countably many have finitely presented envelopes by
shift-envelope-fp-enumerations-are-countable. Hence f also has a bad
extension. Basic finite-agreement neighborhoods have no isolated points;
each singleton is nowhere dense. The countable good locus is therefore
meagre and its complement comeagre. Both are dense by the preceding
arguments.

This does not turn the cardinality argument into an effective procedure
for producing a bad extension, and it does not decide the word problem
of an arbitrary envelope.

