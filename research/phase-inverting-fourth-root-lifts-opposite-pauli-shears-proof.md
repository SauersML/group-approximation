---
rg: 2
id: phase-inverting-fourth-root-lifts-opposite-pauli-shears-proof
kind: route
title: Check the phase-corrected images in the sixteen-element normal form
target: phase-inverting-fourth-root-lifts-opposite-pauli-shears
requires: []
---

Every word in `(PIS1)` has a normal form `R^r p^a q^b`, with
`r in Z/4` and `a,b in F_2`, and multiplication

```text
(r,a,b)(s,c,d)=(r+s+2bc,a+c,b+d).                              (PIS4)
```

These sixteen triples form a group satisfying `(PIS1)`, so the normal forms
are distinct.  Since `(pq)^2=R^2`, the element `Rpq` is an involution.  Its
commutator with either `p` or `q` is again `R^2`; meanwhile both maps in
`(PIS2)` send `R^2` to `R^-2=R^2`.  Hence the images satisfy every defining
relation.  Their quotient actions are invertible, and the central generator
also remains a generator, so both endomorphisms are automorphisms.

For `alpha`, applying the map twice to `q` gives

```text
alpha(R p q)=R^-1 p(R p q)=q;
```

the other generators are immediate.  The same calculation proves
`beta^2=1`.  Direct substitution on `R,p,q` gives `(alpha beta)^3=1`; its
quotient action is a nontrivial order-three element, so the order is exactly
three.  The artifact exhaustively checks multiplication, bijectivity,
relation preservation, both involution identities, and the product order.
