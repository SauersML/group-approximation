---
rg: 2
id: arbitrary-benign-witness-fold-refinement-counterexample-proof
kind: route
title: Put a free subgroup inside a finitely presented simple group with no finite quotients
target: arbitrary-benign-witness-fold-refinement-counterexample
requires:
  - thompson-v-not-lef
---

Thompson's group `V` is finitely presented, infinite and simple, so every map
from `V` to a finite group is trivial.  It contains a nonabelian free subgroup
`e(F_2)` (for example through the standard ping-pong subgroup of Thompson's
circle group `T<=V`).  Set `N=L=1` and `K=V`.  Then

```text
e(F_2) cap L=e(N),
```

so `(K,e,L)` satisfies the benign-witness hypotheses, while `F_2/N` is
residually finite.

Because `L=1`, the rope ambient is `Gamma=V*<v>`.  Every finite quotient of
`Gamma` kills the `V` factor, and therefore kills both generators of
`S=<e(F_2),v e(F_2)v^-1>`.  For a proper finite-index normal `F'` of `F_2`,
the fold `S->F_2/F'` is nontrivial, so its kernel cannot contain all of `S`.
This contradicts the required containment

```text
S cap ker(alpha) <= ker(S -> F_2/F')
```

for every possible finite quotient `alpha` of `Gamma`.

Finally choose `k in V\e(F_2)`.  If `k` belonged to `S`, applying the free
product retraction `Gamma->V`, `v->1`, would put `k` in `e(F_2)`, a
contradiction.  Yet every finite quotient sends `k` to `1`, which belongs to
the image of `S`.  Thus `k` is in the profinite closure of `S` but not in
`S`, refuting closedness as well.
