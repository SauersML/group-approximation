---
rg: 2
id: nonhyperlinear-presentation-sigma2-bound-proof
kind: route
title: Combine finite equality proofs with decidable matrix feasibility
target: nonhyperlinear-presentation-codes-have-a-sigma2-upper-bound
requires:
  - word-problem-of-finite-presentation-is-re
---

Let `P=<S|R>` be finite and let `W_n` be the words in `S` of length at most
`n`.  Use rational squared-norm thresholds tending respectively to zero and
two; changing finitely many initial scales is harmless.

If `P` presents a hyperlinear group, partition `W_n` according to equality
with the identity.  Every word in the equality part has some finite van
Kampen proof, and a canonical-trace microstate simultaneously separates the
finite complement while making every relator small.  Strict inequalities
persist under a small perturbation, so the corresponding real
semialgebraic feasibility statement holds.

For completeness, the canonical-trace normalization does not have to be
assumed in the definition of hyperlinearity.  Start with a tuple separating
one nontrivial word `w`.  Direct-sum it with the trivial tuple.  The normalized
trace of `w` becomes

```text
z_w=(1+tr(w(U)))/2,
```

whose modulus is bounded below one whenever `w(U)` stays a definite HS
distance from the identity.  Tensor powers make `z_w^k` arbitrarily small.
For finitely many target words, perform this construction for each target
and tensor the resulting tuples: the trace of each target product has its own
small factor, while the relator defect of a tensor product is at most the sum
of the factor defects.  Choosing the input defects after the finite tensor
exponents are known gives one simultaneous tuple with traces near zero, hence
squared distances near two.  Complex-conjugate direct sums may additionally
make all intermediate traces real, but are not essential.

Conversely, suppose certificates exist at every scale.  A genuinely
nontrivial word can never occur in the equality part because that part comes
with a valid derivation.  It is therefore separated in every sufficiently
large certified microstate.  Taking a diagonal metric ultraproduct over the
certified tuples kills the finite relator set and gives squared distance two
from the identity for every nontrivial word.  Hence the presented group
embeds in a tracial matrix ultraproduct and is hyperlinear.

Encode the partition, all derivations, and `d` by one natural number `m`.
Tarski decision for the remaining fixed-dimensional feasibility problem
makes the certificate predicate `C(P,n,m)` decidable.  Thus

```text
P in HYP       iff  forall n exists m C(P,n,m),
P notin HYP    iff  exists n forall m not C(P,n,m),
```

which is the claimed `Pi^0_2/Sigma^0_2` membership pair.  No reduction from
a complete set is constructed, so no hardness adjective is justified.
