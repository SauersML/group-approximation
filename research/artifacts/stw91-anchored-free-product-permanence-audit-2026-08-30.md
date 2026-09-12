---
title: Anchored reduced-free-product permanence audit (2026-08-30)
---

## Closure

One selfless factor is enough to make an arbitrarily indexed reduced free
product selfless, provided every other factor is separable and has
faithful-GNS state.  For countable discrete groups, one selfless reduced
group algebra therefore makes the free product with any countable family of
arbitrary countable groups selfless.

This closes two graph nodes:

- `robert-selfless-free-product-absorption`, the exact binary literature
  input;
- `stw91-anchored-arbitrary-free-products-are-selfless`, the arbitrary-family
  permanence theorem obtained by finite induction and a dense directed union.

It does not assert the universal statement in STW Problem XCI: a group with
no known selfless free factor remains outside the argument.

## Primary-source hypothesis audit

The primary source is Leonel Robert, *Selfless C*-algebras*,
arXiv:2309.14188v3 (6 June 2025), published in *Advances in Mathematics* 478
(2025), article 110409, DOI `10.1016/j.aim.2025.110409`.

The exact inputs are:

1. Theorem 4.2: if `(A,rho)` is selfless and `(B,tau)` is separable with
   faithful GNS representation, then `(A,rho)*(B,tau)` is selfless.  The
   source explicitly removes separability of `A`; it does not require `B` to
   be selfless, exact, nuclear, simple, or tracial.
2. Theorem 4.1: if a C*-probability space is the norm closure of an upward
   directed family of unital selfless C*-probability subalgebras, then it is
   selfless.  The theorem imposes no countability condition on the index set.
3. The proof of Theorem 2.8 uses the same finite-subset realization needed
   here: finite reduced free products are regarded as subalgebras of the full
   reduced free product, form an upward directed family, and have dense
   union.
4. Theorem 3.1 supplies the tracial consequences used in the group
   corollary: simplicity, stable rank one, strict comparison, and uniqueness
   of the normalized 2-quasitrace.

The arXiv v3 HTML and the publisher record were checked directly.  This audit
also corrects the pre-existing repository citation from article number
`110403` to `110409`.

## Proof of the new permanence step

Fix the selfless anchor `i_0`.  For a finite set `F` containing `i_0`, let

```text
D_F = *_(i in F) (A_i,rho_i).
```

Induction on `|F|` proves `D_F` selfless.  The base is the anchor.  At each
successor step, associativity writes the new packet as `D_F*A_j`; Theorem
4.2 applies because `A_j` is separable and has faithful-GNS state.

The finite sets containing `i_0` are directed by union.  Their canonical
free-product subalgebras have dense union because each algebraic reduced word
mentions only finitely many indices.  Theorem 4.1 now gives selflessness of
the full product.  This proof works for an uncountable factor index set and a
nonseparable anchor.

## Boundary checks

- The anchor cannot be omitted: the proof needs a selfless base stage.
- Separability is required for every factor added through Theorem 4.2.  The
  separate in-repository binary theorem permits a nonseparable added factor
  only when that factor is itself selfless.
- Faithful GNS representation is part of Robert's free-product framework and
  is retained explicitly.
- No claim about full free products or amalgamated reduced free products is
  made.
