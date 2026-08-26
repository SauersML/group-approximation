---
rg: 2
id: fournier-facio-purely-singular-free-near-representation
kind: claim
title: The Fournier--Facio group admits a purely singular essentially free amenable near representation
distinct_from:
  fournier-facio-hyperlinear-iff-singular-near: That proves this witness is equivalent to hyperlinearity; this is the unresolved existence assertion itself.
  wreath-amenable-near-representation: That asks for a witness for the Kun--Thom wreath; this concerns the separate torsion-free Fournier--Facio candidate.
---

For the finitely presented torsion-free Fournier--Facio group `G`, construct
a Hilbert space `H`, a purely singular invariant state `phi` on `B(H)`, and a
`phi`-near representation `pi:G -> U(H)` satisfying

```text
phi(pi(g))=0                    for every g != 1.
```

By `fournier-facio-hyperlinear-iff-singular-near`, this is exactly the
positive hyperlinearity branch for `G`, not an auxiliary permanence
condition.

## Attempts

The operator-norm and unnormalized-Frobenius models already in the graph do
not furnish the witness: their stability is degenerate asymptotic triviality,
whereas essential freeness requires the regular character.  A normal
invariant state is also impossible by the established minimal almost
periodicity/pure-singularity reduction.  The remaining construction must use
a genuinely singular finitely additive charge, and no such charge is presently
known for the full Fournier--Facio compression group.

Two broad singular-charge constructions are now excluded, not merely left
untested.  `fournier-facio-compression-coset-charge-impossible` kills every
induced or Banach-limit basis carrying an equivariant map to `G/Gamma`, since
the charge would push down to a forbidden invariant mean.
`fournier-facio-monomial-near-witness-impossible` kills every remaining
phase-twisted Schreier/permutation basis: forgetting phases would give an
essentially free amenable near action and hence soficity.  A positive witness
must therefore be both singular and genuinely non-Cartan, mixing basis
vectors on positive charge with no equivariant coarse coset factor.
