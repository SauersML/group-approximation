---
rg: 2
id: stw40-restrict-state-space-amenability-to-trace-boundary-proof
kind: route
title: Restrict state-space amenability to the extracted trace boundary
target: stw40-trace-simplex-boundary-is-topologically-amenable
requires:
  - stw40-trace-simplex-contains-a-nontrivial-boundary
---

Ozawa--Suzuki, Proposition 3.5 in [*On characterizations of amenable
C-star-dynamical systems and new
examples*](https://doi.org/10.1007/s00029-021-00699-2) ([arXiv:
2011.03420](https://arxiv.org/abs/2011.03420)), proves that an amenable action
on a unital C-star algebra induces a topologically amenable action on its
weak-star compact state space.  (The published erratum concerns the
nonunital formulation and is irrelevant here.)

Apply this to `alpha:G acts on A`.  If

```text
m_i:S(A) -> Prob(G)
```

are the continuous probability-valued witnesses, then their restrictions to
the closed invariant subspaces

```text
X subset T(A) subset S(A)
```

obey exactly the same uniform equivariance estimates.  Hence the boundary
`X` extracted by
`stw40-trace-simplex-contains-a-nontrivial-boundary` is topologically
amenable.  Its already established minimality and strong proximality make it
an amenable `G`-boundary.
