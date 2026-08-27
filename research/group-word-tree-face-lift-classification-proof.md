---
rg: 2
id: group-word-tree-face-lift-classification-proof
kind: route
title: Classify finite group-word lifts in the Bass-Serre tree and collapse their kernel gauges
target: group-word-tree-face-balancing-collapses
requires:
  - three-face-ucp-balancing-needs-macroscopic-tree-motion
  - kernel-inner-tree-face-balancing-collapses
artifacts:
  - research/artifacts/caprace-muehlherr-maximal-bounded-ucp-audit-2026-08-25.md
---

Write `A=P_12`, `B=P_23`, `C=P_2`, and let
`q:G_0=A *_C B ->> Lambda` have kernel `K`.  We first prove the finite
subgroup-lift classification used in `(GW6)`.

Let `V` be either `A` or `B`, and let

```text
alpha:V->G_0,             q alpha(v)=v for every v in V.    (1)
```

The map `alpha` is injective.  Its finite image fixes a vertex of the
Bass--Serre tree of `A *_C B`, so for some `h in G_0` and
`W in {A,B}`,

```text
alpha(V) <= h W h^(-1).                                  (2)
```

After applying `q`, the finite subgroup `q(h)Wq(h)^(-1)` contains `V`.
By maximal finiteness of `V` in `Lambda`, equality holds.  Thus `V` is
conjugate to `W`.  The nonconjugacy hypothesis forces `W=V`; since the two
finite groups in `(2)` then have the same order, `(2)` is equality.

Put `beta=Ad(h^(-1)) alpha`, an automorphism of `V`.  Equation `(1)` gives

```text
q(h) q(beta(v)) q(h)^(-1)=v,             v in V.           (3)
```

In particular `q(h)` normalizes `V`.  Self-normalization gives
`q(h)=p in V`.  Since `q` is injective on the finite face `V`, `(3)` implies

```text
beta(v)=p^(-1) v p.                                       (4)
```

Consequently

```text
alpha(v)=h p^(-1) v p h^(-1)=k v k^(-1),
k:=h p^(-1) in K.                                         (5)
```

This proves `(GW6)` for both tree faces.

Now suppose `Phi` satisfies `(GW4)--(GW5)`.  Because a unital star
homomorphism sends products of the canonical finite-group unitaries to
products, and those images are group unitaries, its restrictions give the
homomorphisms `alpha_12,alpha_23` above.  Choose `k_12,k_23 in K` as in
`(5)`.  The restrictions of one linear map agree on the common algebra
`C^*(C)`, hence for every `c in C`,

```text
k_12 c k_12^(-1)=k_23 c k_23^(-1).
```

Therefore `k_23^(-1)k_12` belongs to `K intersect C_(G_0)(C)`, which is
trivial by `(GW3)`.  Write the common conjugator as `k` and set

```text
Psi=Ad(u_k^*) o Phi.
```

Then `Psi` is ucp and canonical on both `C^*(P_12)` and `C^*(P_23)`.
For a nontrivial closing-face kernel cycle
`n=a_1...a_L`, `a_j in P_1 union P_3`, every `a_j` is also a tree-face
letter.  Hence

```text
Psi(u_(q_E(a_j)))=u_(a_j)       for every j.               (6)
```

Equation `(6)` contradicts
`three-face-ucp-balancing-needs-macroscopic-tree-motion`, which forces one
of these values to move by at least `2/L^2`.  This proves the claim.

It remains to verify that this criterion applies to the explicit example,
rather than leave the theorem conditional.  Start before quotienting by the
finite centre.  For a maximal spherical subset `I` of the rank-three Coxeter
set, the standard finite-type Levi `L_I` is the intersection of the
stabilizers of a pair of opposite maximal spherical residues of type `I`.
The converse direction of Caprace--Muehlherr Theorem 4.1 says that this
intersection is a maximal bounded subgroup and is in case (i).  Their
Corollary 3.8 says that bounded subgroups are exactly finite subgroups over
the finite field.  Hence every `L_I` is maximal finite.

The same theorem says that the positive and negative residues stabilized by
`L_I` are unique.  If `g` normalizes `L_I`, then `g` permutes each singleton
set of stabilized residues, hence fixes both residues and belongs to their
stabilizer intersection `L_I`.  Therefore `N(L_I)=L_I`.  Also, conjugation
by the Kac--Moody group preserves residue type.  Since `{1,2}` and `{2,3}`
are distinct maximal spherical types, `L_12` and `L_23` are not conjugate.

All three statements pass through the finite central quotient.  Indeed, the
full inverse image of a finite subgroup containing the image of `L_I` is a
finite subgroup containing `L_I`, proving maximality; the full inverse image
of a normalizer is a normalizer modulo the common centre, proving
self-normalization; and a conjugacy downstairs lifts to a conjugacy of the
full inverse images, contradicting the type argument.  Thus `(GW1)--(GW2)`
hold for the centre-free `(3,3,4)` lattice.  Finally
`kernel-inner-tree-face-balancing-collapses` proves

```text
C_(G_0)(P_2)<=P_2,              K intersect P_2={1},
```

and hence `(GW3)`.  The abstract argument above is therefore unconditional
at that instance.
