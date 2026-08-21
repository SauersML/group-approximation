---
rg: 2
id: schreier-matchings-kill-alternating-forms
kind: claim
title: Involutive Schreier matchings uniformly kill every alternating commutator form
distinct_from:
  two-field-matchings-rigidify-linear-weyl-mislabels: that obtains a uniform gap for the two primitive field matchings by a degree-two Reed--Muller argument; this uses a bounded involutive Cayley expander and is the representation-theoretic class-two input for a stronger sampler.
  dimension-expander-two-matching-square-function: that asks for the full operator-valued matrix-block ledger; this proves only the exact class-two exterior-square energy inequality.
---

ESTABLISHED.  Let `V=F_2^n`, `n>=3`, and let `S` be a finite set of
involutions generating `SL(V)=GL(V)`.  Normalize the Cayley spectral gap
`lambda` by requiring that every unitary representation `pi` and vector `f`
satisfy

```text
E_(s in S) ||pi(s)f-f||^2 >= lambda ||f-P_inv f||^2,          (IS1)
```

where `P_inv` projects onto the invariant vectors.  For an alternating
binary bilinear form `B`, put

```text
q_s(b)=B(sb,b),
delta=E_(s,b) 1_(q_s(b)=1).                                  (IS2)
```

If `B!=0`, then

```text
delta >= lambda/18.                                           (IS3)
```

Thus the identity matching, which makes the class-two residual alternating,
together with the matchings `a=sb`, `s in S`, has a dimension-independent
soundness gap against every nonzero exterior-square/linear-Weyl error.  In
the associated class-two quotient of the double weak-commutativity group,
the mixed commutator module is

```text
(V tensor V)/span{b tensor b:b in V} = exterior^2 V.          (IS4)
```

Polarizing `q_s=0` says that an involution `s` preserves its residual form.
Since `GL_n(2)` preserves no nonzero alternating form for `n>=3`, exact
rigidity follows already from generation; `(IS3)` is its uniform robust
version.

## Scope

This does not yet control the nonlinear Sidki `R` layers or arbitrary
matrix-block multiplicity.  The full robust metapixel needs an orthogonal
square function which applies the same Schreier gap to every exterior layer
without paying once per nilpotency degree.  That target is isolated in
`schreier-square-function-for-weak-commutator-layers`.
