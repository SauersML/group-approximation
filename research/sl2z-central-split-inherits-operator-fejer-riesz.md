---
rg: 2
id: sl2z-central-split-inherits-operator-fejer-riesz
kind: claim
title: Central splitting imports bounded operator Fejer--Riesz inside each modular vertex
distinct_from:
  relative-induced-selector-gap-has-bounded-dual-witness: that gives the dual separator for the full relative Iwahori selector; this factors positive operator-valued polynomials inside one exact modular vertex and explains why those are different cones.
  iwahori-local-global-defect-question: that asks for uniform repair across the infinite Iwahori edge; this closes only the finite central amalgam internal to each modular vertex.
  finite-index-double-theorem-misses-iwahori-twist: that fences an MF theorem for an untwisted double; this audits an operator-valued sums-of-squares theorem and locates its failure at quotient positivity.
---

Use the standard presentation

```text
Lambda=SL_2(Z)=C4 *_(C2) C6
 = <u,v | u^4=v^6=1, u^2=v^3>.
```

Let `z=u^2=v^3` and `e_+=(1+z)/2`, `e_-=(1-z)/2`. For a
separable Hilbert space `E`, every positive operator-valued
trigonometric polynomial

```text
p in B(E) tensor C[Lambda]
```

of amalgamated syllable extent `d` admits a factorization

```text
p=sum_j q_j* q_j,                                      (MCF1)
```

where every `q_j` has amalgamated syllable extent at most

```text
floor(d/2)+1.                                          (MCF2)
```

Thus the finite central `C2` amalgam does not obstruct the explicit
operator-valued Fejer--Riesz theorem of Jindal--Klep--McCullough,
[arXiv:2604.27062](https://arxiv.org/abs/2604.27062), Theorem B.

The reason is an exact central-character splitting. The two corners satisfy

```text
e_+ C*(Lambda) isomorphic to C*(C2*C3),
e_- C*(Lambda) isomorphic to C*(C2*C3).                (MCF3)
```

In the positive corner the order-two and order-three generators are
`e_+u,e_+v`. In the negative corner they may be taken as
`i e_-u,-e_-v`. Apply Theorem B in the two corners and add the
orthogonal sums-of-squares factorizations.

The factors can also be lifted termwise through the quotient

```text
C4*C6 -> C4 *_(C2) C6.
```

Choosing the lift of the leading central letter inside the first syllable
preserves the extent bound. Thus `p` is the image of an upstream positive
polynomial already written as controlled sums of squares.

This positive result does not bound the authenticated Iwahori selector

```text
Delta_(N,beta)(X).
```

The bounded dual witness for that selector separates relative ucp maps on
the finite quotient `A_N`, with exact values on the entire BS core. It is
not a positive polynomial on one modular vertex. Theorem B assumes
positivity in every representation of a scalar free product; the Iwahori
dual cone imposes an infinite edge identification and the translated
normal-closure rows.

The mismatch is algebraically sharp. If `q:W->H` is a group quotient,
`r` is a killed relation word, and

```text
p_r=-(u_r-1)*(u_r-1),
```

then `q(p_r)=0` is positive in `C*(H)`, while `p_r` is negative and
nonzero in `C*(W)` whenever `r` is nontrivial there. Hence positivity
on the amalgamated quotient cannot be fed to a free-product
Positivstellensatz by choosing the same polynomial upstairs. A new
relative Positivstellensatz would have to add relation-ideal corrections
with extent controlled uniformly over the moving levels `N`.

Consequently the 2026 factorization theorem completely handles the
internal `C2` identification but supplies neither the Iwahori
positive-definite window nor the bounded support inequality (BDW4).
The surviving gate is a uniform sums-of-squares or complete-order theorem
modulo the moving Iwahori normal-closure ideal. The nonhyperlinear-group
root remains open.

DERIVATION
sl2z-central-character-fejer-riesz-proof
