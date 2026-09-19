---
rg: 2
id: manzoor-native-haar-envelope-is-ce-after-corners
kind: claim
title: The Manzoor source has no native algebraic Haar envelope even after corners
distinct_from:
  manzoor-natural-subgroup-subshift-is-not-a-haar-envelope: that audits the concrete subgroup-indicator, pseudo-subgroup and labeled-Schreier spaces in the primary proof; this rules out every algebraic Haar crossed product with the native free actor by Connes embeddability, including expected embeddings and amplifications.
  free-actor-extensions-cannot-host-nonce-relation: that treats arbitrary pmp extensions by a free actor and the singular Feldman--Moore quotient; this gives the shorter Pontryagin-dual obstruction for algebraic actions and records stability under corners.
  abelian-by-virtually-free-groups-are-sofic: that proves the group-theoretic permanence theorem; this applies it to the actual non-CE Manzoor GNS and relation factors.
---

**ESTABLISHED SOURCE-SPECIFIC OBSTRUCTION.**  Let `F` be the nonabelian free
group carrying Manzoor's ergodic non-co-hyperlinear IRS `H`, and put

```text
N=L(F/H).                                               (MNC1)
```

Thus `N` is not Connes embeddable.  Let `K` be any compact second-countable
abelian group on which `F` acts by continuous group automorphisms, and let
`A=hat K`.  Then

```text
M=L^infinity(K,Haar) rtimes F  ~=  L(A rtimes F).       (MNC2)
```

The semidirect product in `(MNC2)` is sofic: `A` is amenable and the quotient
`F` is sofic, so amenable-extension permanence applies.  Hence `M` is Connes
embeddable.

Connes embeddability passes to von Neumann subalgebras, matrix
amplifications and finite corners.  Conversely, a nonzero amplification or
corner of a finite factor is Connes embeddable only if the factor is.  It
follows that neither `N`, the non-CE relation factor `L(R)` containing `N`,
nor any nonzero corner/amplification of either can embed trace-preservingly
into a corner or amplification of `M`.

The word **expected** does not weaken this obstruction.  Every von Neumann
subalgebra of a finite tracial von Neumann algebra has its trace-preserving
normal conditional expectation.  Thus a trace-preserving embedding here is
automatically expected.

This applies directly to the actual Manzoor construction.  The paper first
chooses an unnamed separating IRS by compact convex separation, realizes it
as the stabilizer law of a pmp action `F curvearrowright (X,mu)`, and embeds
`N` in the Feldman--Moore algebra `L(R_X)`.  The algebraic crossed-product
map

```text
L^infinity(X) rtimes_alg F -> L(R_X)                    (MNC3)
```

which identifies group elements inducing the same orbit arrow is a singular
quotient and cannot extend normally: a normal extension would make the
non-CE target a direct summand of the CE free-action crossed product.  The
subgroup subshift and the relatively Bernoulli labeled-Schreier realization
do not alter this conclusion; they are not one compact abelian group with
Haar measure, as detailed in
`manzoor-natural-subgroup-subshift-is-not-a-haar-envelope`.

Therefore the actual source supplies no algebraic/Bernoulli shortcut to
`non-ce-relation-admits-algebraic-action-envelope` with its native actor,
even after every standard corner or expectation relaxation.  A successful
envelope must use a genuinely different acting group `Lambda`.  If such a
`K,Lambda` and trace-preserving inclusion were constructed, Pontryagin
duality would immediately make `hat K rtimes Lambda` non-hyperlinear; that
would be the breakthrough itself, not structure already latent in Manzoor's
proof.

Primary source: A. Manzoor,
[*There Is An Equivalence Relation Whose von Neumann Algebra Is Not Connes
Embeddable*](https://arxiv.org/abs/2502.06697v2), Proposition 2.11,
Definition 2.12, and the joint proof of Theorems 1.1--1.2.

DERIVATION
manzoor-native-haar-corner-fence-proof

