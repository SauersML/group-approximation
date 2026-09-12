---
rg: 2
id: atlas-six-relator-chart-injection-proof
kind: route
title: Evaluate the asymmetric one-chart relators in an arbitrary quotient
target: atlas-six-relator-nontrivial-quotients-inject-charts
requires:
  - atlas-six-relator-natural-orbit-mixing-floor
---

Let `q:Gamma_6 -> Lambda`.  Since `A8` is simple, the kernel of each chart
restriction is either trivial or the whole chart.

The exact one-chart evaluations frozen in
`atlas-six-relator-natural-orbit-mixing-floor` are identities in the abstract
factor, not facts special to a permutation representation.  After setting
the first chart equal to `1`, the word `s_0` reduces to a fixed nonidentity
element of the second `A8`.  After setting the second chart equal to `1`, the
word `s_11` reduces to a fixed nonidentity element of the first `A8`.

Therefore the first restriction cannot be trivial while the second is
injective: the defining equation `q(s_0)=1` would kill a nonidentity element
of the injected second chart.  The symmetric case contradicts
`q(s_11)=1`.  If both restrictions are trivial, then `q` is trivial because
the two marked factors generate `Gamma_6`.  The only remaining nontrivial
case has both restrictions injective.

Nothing in this argument uses finite-dimensionality, residual finiteness,
or hyperlinearity.  The finite-simple reduction had used the same two literal
evaluations after choosing a finite image; the quotient-rigidity statement
holds before that choice.

