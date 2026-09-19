---
rg: 2
id: stw08-continuous-block-gluings-preserve-af-embeddability
kind: claim
title: Finite continuous-block gluings preserve trace-compatible AF-embeddability
distinct_from:
  stw08-finite-group-crossed-products-preserve-af-embeddability: that uses a finite regular covariant matrix representation; this uses Cantor covers and coordinate embeddings and applies to continuous fields, arbitrary subalgebras, and pullbacks without an action.
  stw07-surjective-pullbacks-preserve-nuclear-qd-finiteness: that needs one gluing map surjective to recover nuclearity from an extension; this embeds the pullback directly into an AF algebra and requires no surjectivity.
  stw99-problem-viii-exact-quasidiagonal-af-embeddable: this transports AF embeddings already available on finitely many coefficient algebras and does not create one from abstract quasidiagonality.
artifacts:
  - research/artifacts/stw08-af-embedding-status-and-coherence-audit-2026-08-30.md
---

Let `X_1,...,X_m` be second-countable locally compact Hausdorff spaces, and
let `A_1,...,A_m` be AF-embeddable C*-algebras.  Then every C*-subalgebra

```text
P subseteq direct_sum_(j=1)^m C_0(X_j,A_j)             (1)
```

is AF-embeddable.

Consequently, arbitrary finite pullback trees whose leaves are continuous
blocks `C_0(X_j,A_j)` are AF-embeddable.  No gluing map has to be surjective.
This includes mapping tori of pairs of homomorphisms between AF-embeddable
algebras and, by taking finite-dimensional coefficient algebras, every finite
recursive subhomogeneous construction.

There is also a trace-compatible unital version.  Suppose the `X_j` are
compact, `A_j` and `E_j` are unital, and `tau_j` is a faithful tracial state
on `A_j` which extends across a unital AF embedding `eta_j:A_j->E_j` to a
tracial state `sigma_j` on `E_j`.  Let `P` contain the unit of the ambient
finite direct sum.  If `mu_j` is a full-support probability measure on
`X_j`, and `lambda_j>0` with `sum_j lambda_j=1`, then

```text
Theta((f_j)_j)=sum_j lambda_j integral_(X_j) tau_j(f_j(x)) d mu_j(x)
```

is a faithful tracial state on `P`, extends across the constructed unital AF
embedding of `P`, and is therefore quasidiagonal.  Thus these traced gluings
give unconditional trace-preserving positive instances of Problem IX(2),
while the untraced assertion gives a permanence class for Problem VIII.
