---
rg: 2
id: canonical-fano-free-product-defeats-finite-actor-payment
kind: claim
title: A canonical free Fano cap defeats every finite Bass-Serre payment actor
artifacts:
  - experiments/or3_fano_cap_free_product_trace.py
distinct_from:
  canonical-types-extend-every-finite-bass-serre-actor: that proves extension for every canonical base type but does not identify a payload which remains macroscopically unpaid; this computes the exact OR3 cap commutator left by such an extension.
  raw-prefix-covariance-reduces-to-nonincidence-cap-commutators: that isolates nonincidence commutators as the sufficient SPA12 payload; this proves that finite actors and canonical moment tests cannot pay even one uncompressed instance of that payload.
---

**ESTABLISHED FINITE-ACTOR NO-GO.**  Let `A=C_2^3`, write its character
projections as `e_v`, and fix nonzero `lambda in F_2^3`.  The four-character
OR3 Fano-cap projection is

```text
q_lambda=sum_(lambda dot v=1)e_v=(1-a_lambda)/2.       (CFP1)
```

Let `t` generate a free `C_2` factor and put

```text
Gamma_0=A*C_2.                                        (CFP2)
```

In the canonical trace of `Gamma_0`,

```text
tau(q_lambda)=1/2,
tau(t q_lambda t q_lambda)=1/4,
||[t,q_lambda]||_2^2=1/2.                             (CFP3)
```

Indeed the first identity is immediate from `(CFP1)`.  In the free-product
normal form, a term of `tq_lambda tq_lambda` is the identity only when both
`A`-letters are the identity, giving the square of the identity coefficient
of `q_lambda`.  Expanding the commutator square then gives

```text
||[t,q_lambda]||_2^2
 =2 tau(q_lambda)-2 tau(tq_lambda tq_lambda)=1/2.      (CFP4)
```

The artifact performs the complete rational group-algebra calculation.  It
also reconstructs `q_lambda` by summing its four Fourier character atoms and
checks `(CFP1)` coefficientwise.

Now attach any finite graph-of-groups actor to `Gamma_0`, with finite
auxiliary vertex and edge groups and arbitrary finite-subgroup HNN loops.
The virtually free group `Gamma_0` has a canonical matrix-ultraproduct
embedding.  By `canonical-types-extend-every-finite-bass-serre-actor`, that
embedding extends through the actor with every actor relator exact.  Its
restriction to `Gamma_0` remains canonical, so `(CFP4)` is unchanged.

Consequently no estimate of the form

```text
||[t,q_lambda]||_2^2
 <=C (finite Bass--Serre actor energy)+o_canonical(1)  (CFP5)
```

can hold.  Canonical moment tests make the obstruction stronger rather than
weaker: they pin the left side to `1/2`.  This rules out every finite packet,
finite-subgroup transporter, or finite graph-of-groups realization of the
uncompressed payment `(NCP1)`, including any fixed finite collection of such
actors combined into one graph.

The theorem does not rule out the weaker prefix-compressed payment allowed in
`canonical-or3-nonincidence-cap-commutator-payment`.  A surviving construction
must couple a non-Bass--Serre two-cell or infinite actor to that compressed
payload; freely extendable finite covariance data cannot do it.

