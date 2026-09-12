---
title: PHP crossed-product selflessness audit (2026-08-30)
---

## Closure

A PHP group acting by approximately inner automorphisms on a simple unital
uniquely tracial C*-algebra has a selfless tracial reduced crossed product.
Hence the crossed product is simple, has stable rank one and strict
comparison, and has a unique normalized 2-quasitrace.  Every action of a PHP
group on the Jiang--Su algebra is a concrete special case.

This closes three graph nodes:

- `gjkepr-php-crossed-product-expectations-are-selfless`, the exact relative
  literature theorem;
- `gjkepr-simple-unique-trace-bases-scalarize-selfless-expectations`, the
  general scalarization consequence of the source's composition theorem;
- `stw91-php-approximately-inner-crossed-products-are-selfless`, the new
  tracial crossed-product synthesis and regularity package.

It does not settle STW Problem XCI for all C*-simple groups: the PHP
hypothesis remains, and the coefficient action must be approximately inner.

## Primary-source hypothesis audit

The primary source is David Gao, Marius Junge, Srivatsav Kunnawalkam
Elayavalli, Gregory Patchell, and Leonel Robert, *Selfless
C*-correspondences, operator valued C*-probability spaces and completely
positive maps*, arXiv:2607.20361v1 (22 July 2026).

The exact inputs are:

1. Theorem 9.2, announced as Theorem 1.4: if a discrete PHP group acts on a
   unital C*-algebra `B` by approximately inner automorphisms, then the
   canonical expectation `E:B rtimes_r G -> B` is selfless.  The theorem has
   no separability, exactness, nuclearity, simplicity, or trace hypothesis.
2. Theorem 7.8(iv): if `(A,E,B)` is selfless and `F:B -> C` is an
   approximately selfadjoint-inner expectation, then `(A,F compose E,C)` is
   selfless.
3. The proof of Corollary 7.9: for a simple unital algebra with unique trace
   `tau`, Haagerup--Zsidó's Dixmier theorem makes
   `b |-> tau(b)1_B` approximately inner; since its range is scalar, the
   source observes that it is approximately selfadjoint inner.
4. Immediately after Theorem 1.4, the authors state that every automorphism
   of the Jiang--Su algebra is approximately inner and explicitly conclude
   that `(Z rtimes_r G,tau_Z compose E)` is selfless for every action of a
   PHP group.
5. Robert, *Selfless C*-algebras*, arXiv:2309.14188v3, Theorem 3.1 supplies
   the tracial regularity consequences.

The arXiv v1 HTML was checked at both the introduction and the numbered
results in Sections 7 and 9.  The source was submitted on 22 July 2026; no
later arXiv version was listed on 30 August 2026.

## Proof of the new synthesis

Set `A=B rtimes_(alpha,r) G`.  Theorem 9.2 makes `(A,E,B)` selfless.  Put
`F(b)=tau(b)1_B`.  By the proof of Corollary 7.9, `F` is approximately
selfadjoint inner, so Theorem 7.8(iv) makes `F compose E=tau compose E`
selfless.  The canonical reduced-crossed-product expectation is faithful,
and `tau` is faithful because `B` is simple, so this scalar state has faithful
GNS representation as required.

Because `tau` is unique, it is fixed by every automorphism of `B`.  Thus it
is `alpha`-invariant, and the usual algebraic crossed-product calculation
shows that `tau compose E` is tracial.  Robert's Theorem 3.1 now applies.

For `B=Z`, approximate innerness of every automorphism removes the only
action-side restriction.  No outerness, Rokhlin property, amenability of
`G`, or nuclearity of the crossed product is used.

## Boundary checks

- PHP is essential to the cited compressor theorem; C*-simplicity alone is
  not substituted for it.
- Approximate innerness is required element by element for the action.  The
  proof does not cover arbitrary actions on a general uniquely tracial base.
- Simplicity and uniqueness of trace on `B` enter only at scalarization.
  Without them, the scalar trace map need not be approximately
  selfadjoint inner by the cited argument.
- The result concerns reduced crossed products and their canonical faithful
  expectation, not full crossed products.
- The Jiang--Su special case is unrestricted only because the source
  explicitly supplies approximate innerness of all its automorphisms.
