---
rg: 2
id: permutation-camouflage-action-proof
kind: route
title: Permute star factors and factor every MF-target map through the quotient
target: permutation-camouflage-realizes-countable-actions
requires:
  - camouflage-kernel-is-a-regular-star-amalgam
  - one-universal-kernel-realizes-all-countable-mf-reflections
---

The universal property of the generalized amalgam `(PCA1)` extends every
permutation of `X` to an automorphism: use the identity map on each copy of
`B` and identify all copies of `D` pointwise.  This gives `(PCA2)`.

For a homomorphism `f:W(Q,X)->M` to an MF group, the restriction to each
`B_x` is trivial.  The vertex groups generate `K_X`, so `f` kills `K_X` and
factors uniquely through `pi_(Q,X)`.  This proves `(PCA3)`.  Applying the
same argument to the countable image of every corona homomorphism and
intersecting kernels gives `(PCA4)`.

For a normal subgroup `N normal W(Q,X)`, such an `f` kills `N` exactly when
its unique visible factor `bar f:Q->M` kills `pi_(Q,X)(N)`.  Intersecting
these kernels proves `(PCA4a)`.  If every quotient of `Q` is MF, then
`cl_MF^Q(pi(N))=pi(N)`, so

```text
cl_MF^(W(Q,X))(N)=pi^(-1)(pi(N))=N K_X.
```

Because `K_X=normalClosure(d)`, this is `(PCA4b)`; a quotient is MF exactly
when its defining normal subgroup is MF-closed, equivalently when it contains
`d`.

Each `B_x` is perfect and the vertex groups generate `K_X`, so `K_X` is
perfect.  Every map from `K_X` to an MF group is trivial on every vertex
group, proving full MF radical.  The common element `d` normally generates
each vertex group, hence all of `K_X`.

For `(PCA5)`, choose one point from each orbit.  Generators of `Q` together
with generators of the corresponding vertex groups generate all their
`Q`-translates, so finitely many orbits imply finite generation.  Conversely,
the reduced normal forms of a finite generating set involve only finitely
many vertex indices.  Closing those indices under conjugation by `Q` reaches
only finitely many `Q`-orbits.  If another orbit exists, an element of
`B_x\D` in that orbit is outside the generated subamalgam by normal form.

A `Q`-map `p:X->Y` relabels factors and commutes with the `Q`-actions, hence
induces `(PCA6)`.  Composition and identities are inherited from set maps.
If `p!=p'`, choose `x` on which they differ and `b in B\D`; the images of
`b_x` lie in distinct factors, so normal form makes the functor faithful.
The subamalgam and fold arguments show that the kernel map is injective
exactly when `p` is, and its image contains every target factor exactly when
`p` is surjective.  Since `P_p` is the identity on `Q`, this proves `(PCA6a)`
for the semidirect products as well.

The map is injective on every individual factor; therefore its kernel meets
every conjugate vertex stabilizer trivially and acts freely on the
Bass--Serre tree.  The kernel of `P_p` is the same kernel because `P_p` is the
identity on `Q`, so it is free.  Both source and target MF-target Hom functors
identify naturally with `Hom(Q,M)`, under which precomposition with `P_p` is
the identity.  This proves the categorical MF-equivalence statement.

If there are infinitely many nontrivial fibers, choose disjoint pairs of
indices within distinct fibers.  Retraction onto each corresponding
two-factor fold, followed by a nonzero homomorphism from its nontrivial free
kernel to `Z`, gives independent abelianization coordinates exactly as in
the partition-kernel theorem.  The free kernel therefore has countably
infinite rank, proving `(PCA7)`.

For the finite-presentation assertion, choose finite presentations of `B`
and `Q`, a finite generating set of `S`, and the base factor `B_S`.  Present
`W(Q,Q/S)` by these generators and relations, together with: the generators
of `Q` centralize the common element `d`; and the generators of `S` commute
with the generators of `B_S`.  Conjugates of the base factor give the factors
indexed by `Q/S`, and normal form shows that the displayed relations impose
exactly their common amalgamation over `D`.  This is a finite presentation.

Finally, `<a^(2^(n+1))>` is contained in `<a^(2^n)>`, giving a
`Q`-equivariant surjection `X_(n+1)->X_n`.  It has infinitely many fibers of
size two.  The free group `Q` is MF, so the radical formula makes the hidden
star kernel the exact MF radical at every stage.  The finite-presentation
result and `(PCA7)` finish `(PCA8)`.
