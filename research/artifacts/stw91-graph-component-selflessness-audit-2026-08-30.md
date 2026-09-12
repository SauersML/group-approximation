# Graph-component selflessness audit

Date: 2026-08-30

## Primary sources

1. Felipe Flores, Mario Klisse, Mícheál O Cobhthaigh, and Matteo Pagliero,
   *Selfless reduced free products and graph products of C-star-algebras*,
   [arXiv:2510.24675v3](https://arxiv.org/abs/2510.24675).

   - Theorem A / Theorem 2.7: the Avitzour unitary condition implies complete
     selflessness of a reduced free product.
   - Theorem C / Theorem 2.2: a graph product over a complement-connected
     graph with at least three vertices is completely selfless under one
     centered centralizer unitary at every vertex.
   - Corollary E: graph products of simple separable unital non-elementary
     tracial algebras are completely selfless, provided isolated vertices of
     the complement are labelled by completely selfless factors.

2. Narutaka Ozawa,
   *Proximality and selflessness for group C-star-algebras*,
   [arXiv:2508.07938v7](https://arxiv.org/abs/2508.07938), Theorem 11.

   The tensor product of separable completely selfless probability spaces is
   completely selfless.

3. Leonel Robert, *Selfless C-star-algebras*, arXiv:2309.14188v3,
   Theorems 3.1 and 4.1.

   Tracial selflessness implies simplicity and strict comparison, and
   selflessness passes to norm-dense directed unions.

## Exact group specialization

For a nonidentity group element `g`, the regular unitary `lambda(g)` is in
the centralizer of the canonical trace and has trace zero.  If a group has at
least three elements, it contains distinct nonidentity `h_1,h_2`, and

```text
tau(lambda(h_1)^* lambda(h_2))=0.
```

Thus Flores--Klisse--O Cobhthaigh--Pagliero Theorem A applies to `G*H`
unless both groups have order two.  The excluded free product is the amenable
infinite-dihedral group, whose reduced algebra has a character and is not
simple.  This makes the exception exact.

## Complement-component synthesis

Every graph is the join, over the connected components of its complement, of
the corresponding induced subgraphs.  At the group level its graph product is
the restricted direct product of the induced graph products.

- components of size at least three are handled by Theorem C;
- components of size two are handled by the exact free-product criterion;
- singleton components are precisely universal vertices and retain the
  original vertex-group difficulty.

Finite joins preserve complete selflessness by Ozawa.  Countable joins are
norm-dense directed unions of finite joins and hence preserve ordinary
selflessness by Robert.

## Novelty and remaining frontier

Repository searches for `Avitzour completely selfless`, `C2*C2`,
`complement components selfless`, `no universal vertices`, and the proposed
node identifiers found no existing Cairn version of these results.

This closes XCI, XC, and the unique-quasitrace consequence for graph products
without universal vertices.  It does not settle universal XCI: a universal
vertex is a direct-product factor, and an arbitrary C-star-simple factor is
exactly the unresolved input.