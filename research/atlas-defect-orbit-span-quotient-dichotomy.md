---
rg: 2
id: atlas-defect-orbit-span-quotient-dichotomy
kind: claim
title: Every augmented Atlas defect seed either spans the carrier or leaves an exact faithful quotient
distinct_from:
  atlas-augmented-rank-zero-set-compactness: that promotes an arbitrary asymptotic rank zero by an unspecified lifting mechanism; this constructs an exact finite zero whenever the normal orbit-span of the residual images is proper.
  atlas-mixed-fixed-spaces-are-rank-pencils: that identifies finite mixed tests as rank pencils; this identifies the infinite alternating orbit closure which those finite-depth tests do not control.
  finite-presentation-must-expose-whole-module-with-uniform-defect: that asks a Hilbert--Schmidt presentation to expose an infinite augmentation module; this is an exact finite-field quotient lemma for two repeated natural Atlas charts.
---

Let `V=F2^4` be the natural faithful simple module of
`A8=GL_4(F2)`.  On one finite vector space `E`, let

```text
rho_1,rho_2:A8 -> GL(E)
```

be exact representations, each isomorphic to `V tensor F2^m`.  Let
`rho:A8*A8 -> GL(E)` be the induced free-product representation.  For the
finite augmented Atlas relator set `R_+` (the packet, collision `19243`, and
q14), put

```text
D(rho)=sum_(r in R_+) im(rho(r)-I),
W(rho)=sum_(g in A8*A8) rho(g)D(rho).                  (DOS1)
```

Then exactly one of the following holds:

1. `W(rho)=E`; or
2. `E/W(rho)` is a nonzero exact representation of the augmented Atlas
   quotient `Gamma_+`, and both of its `A8` chart restrictions are faithful
   repeated copies of `V`.                              `(DOS2)`

In particular, if `Gamma_+` has no exact finite faithful-chart model, then
every tuple of exact repeated natural charts satisfies

```text
sum_(g in A8*A8) rho(g)
  sum_(r in R_+) im(rho(r)-I)=E.                       (DOS3)
```

This turns the rank-compactness endpoint into an exact error-propagation
problem.  For a sequence with

```text
dim D(rho_n)/dim E_n ->0,                              (DOS4)
```

it is enough to prove

```text
dim W(rho_n)/dim E_n ->0.                              (DOS5)
```

Indeed `(DOS5)` makes `W(rho_n)` proper for large `n`, and `(DOS2)` gives an
exact finite zero.  A stronger sufficient statement is a constant `C` with

```text
dim W(rho)<=C dim D(rho).                              (DOS6)
```

Equivalently, one may prove a dimension-independent alternating-depth
saturation theorem.  If

```text
W_d(rho)=sum_(word length(g)<=d) rho(g)D(rho),
```

and `W(rho)=W_d(rho)` for one fixed `d`, then

```text
dim W(rho)<=|B_d(A8*A8)| dim D(rho),                  (DOS7)
```

which is `(DOS6)`.

Thus, if an augmented rank microstate exists but no finite escape does, its
vanishing-rank residual images must be a **wandering defect seed**: alternating
the two finite chart actions spreads an `o(dim E)` space onto all of `E`, and
the saturation depth must diverge.  Finite mixed-intersection pencils inspect
only finitely many fixed subspaces/word depths and cannot alone exclude this
scenario.  The binary-specific remaining target is precisely to rule out
this wandering propagation using the fourteen literal two-chart Atlas
relations.  The count thirteen belongs to the virtually-free filling model,
where q14 is already a carrier relation.
