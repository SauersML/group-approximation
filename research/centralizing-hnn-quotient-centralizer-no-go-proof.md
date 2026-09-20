---
rg: 2
id: centralizing-hnn-quotient-centralizer-no-go-proof
kind: route
title: Compute the finite-image edge centralizer and kill closure pinches under exact centralization
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
Britton's lemma says `[v,k]` is nontrivial because `k notin L`. No model
whose base action factors through a finite quotient **and whose stable
letter exactly centralizes the whole edge image** can separate this word.
Approximate centralization of tested edge generators is not excluded:
the length of a word in those generators representing q(k) can grow with
the quotient, so generator-wise errors need not give a vanishing error
for q(k).

For individual pinch separation, allow finite amplification of the
regular quotient action so there are at least three free H-orbits.
Then its equivariant-bijection group C has double centralizer precisely
left translation by H: C is transitive, the stabilizer C_z fixes exactly
Hz, and commutation with C forces any double-centralizing map to equal
one fixed H-translation on every point. Thus q(k) outside H can be
separated by some stable letter in C. This avoids small unamplified
exceptions such as H=1 on a two-point set. Individual-pinch separation
by these exact models is therefore equivalent to separability of L;
no full normal-form separation theorem follows from this alone.

For a Mikhailova edge built from a finitely presented group with
undecidable word problem, membership is undecidable and the edge is
not separable. Membership in a finitely generated separable subgroup
of a finitely presented group is decidable by dovetailing word proofs
with finite-quotient nonmembership certificates. This argument needs
the undecidable-membership hypothesis; it does not assert that every
Mikhailova-type edge is nonseparable.

This proves CE1 and the restricted exact-centralizer no-go. Neither
the approximate-edge variant on quotient bases nor the separate
perturbed-base construction is decided here.
