---
rg: 2
id: centralizing-hnn-quotient-centralizer-no-go-proof
kind: route
title: Compute the free-edge centralizer and kill every profinite-closure pinch
target: centralizing-hnn-sofic-via-regular-edge-centralizer
requires: []
---

Let `q:K -> Q` be a finite quotient, put `H=q(L)`, and let `K` act on `Q`
by left translation.  The restricted `H`-action is free.  After choosing
one point in each orbit, its `H`-set is `H x O`, where `O=H\Q`.  An
`H`-equivariant permutation may independently right-translate each copy of
`H` and permute the copies, so

```text
C_Sym(Q)(H) = H wr Sym(O).
```

Thus every element of this centralizer gives an exact image of the stable
letter in `<K,v | [v,L]=1>`.

Now suppose `k` lies in the profinite closure of `L` but not in `L`.  For
every finite quotient `q`, the definition of profinite closure gives
`q(k) in q(L)=H`.  Hence every possible stable-letter image centralizing
`q(L)` also centralizes `q(k)`, and the word `[v,k]` maps to the identity.
Britton's lemma says `[v,k]` is nontrivial because `k notin L`.  No model
whose base action factors through finite quotients can therefore be a
separating approximation of the HNN extension.

For a finitely generated edge, the quotient-model pinch condition is
equivalent to separability: a stable-letter image separating `[v,k]` exists
in a quotient exactly when some quotient has `q(k) notin q(L)`.  The
Mikhailova edge used by the compiler is not separable.  Indeed, membership
in it is undecidable, whereas membership in any finitely generated separable
subgroup of a finitely presented group is decidable by dovetailing word
proofs (membership) with finite-quotient certificates (nonmembership).
This proves both the exact centralizer formula and the claimed quotient-model
no-go, while making no assertion about the separate perturbed-model lemma.
