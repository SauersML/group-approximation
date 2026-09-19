---
rg: 2
id: stw63-liftable-reduced-product-pairs-are-exactly-conjugate
kind: claim
title: Liftable Jiang--Su pairs in reduced products are exactly unitarily conjugate
distinct_from:
  stw63-uniqueness-is-closed-under-products: that gives approximate uniqueness for arbitrary maps into the product; this passes to a quotient only for pairs with homomorphic lifts and upgrades their conclusion to conjugacy by one quotient unitary.
  stw63-bidual-relative-corners-equivalent: that obtains an implementing sequence after passing from a C-star algebra to its bidual; this works entirely in a norm product and its quotient and explicitly returns a unitary to the quotient.
  stw63-relative-k0-return-criterion: that returns a bidual corner equivalence using K0 injectivity and cancellation in a pair-relative sequence algebra; this uses neither K-theory nor cancellation, but assumes coordinate homomorphic lifts.
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

Let `(B_n)_(n>=1)` be unital C*-algebras, each having approximate unitary
uniqueness for unital Jiang--Su embeddings.  Let `J` be a proper closed ideal
of `product_n B_n` containing `directSum_n B_n`, and put

```text
Q=(product_n B_n)/J.
```

Suppose unital embeddings `phi,psi:Z->Q` admit unital homomorphic lifts

```text
Phi,Psi:Z->product_n B_n.
```

Then there is one unitary `u in Q` such that

```text
u phi(z)u*=psi(z)                         (z in Z).   (1)
```

Consequently, if every unital embedding `Z->Q` has a unital homomorphic lift
to the product, then `Q` is a positive LXIII codomain, with exact unitary
conjugacy rather than merely approximate equivalence.  Conversely, every
LXIII counterexample pair in such a quotient of positive coordinate
codomains must contain at least one nonliftable embedding.
