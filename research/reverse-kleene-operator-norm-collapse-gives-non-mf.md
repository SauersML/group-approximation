---
rg: 2
id: reverse-kleene-operator-norm-collapse-gives-non-mf
kind: claim
title: Reverse Kleene needs only an operator-norm collapse compiler for non-MF
distinct_from:
  reverse-kleene-involutive-compiler-gives-non-mf: That reuses the stronger normalized-HS collapse contemplated by the nonhyperlinear program and converts it to non-MF through a sign-twist HNN wrapper; this is the strictly MF-specific target and quantifies only over operator-norm microstates.
  kleene-halting-mark-collapse-diagonal: That targets nonhyperlinearity and therefore must control normalized-HS microstates, including defects hidden on small-rank sectors; this theorem has no such requirement.
---

Suppose a total computable compiler sends every Turing-machine index `e` to

```text
(Gamma_e=<S_e|R_e>, w_e, delta_e, alpha_e),
```

where `delta_e>0` and `0<=alpha_e<1`, with

```text
machine e halts
  => w_e!=1 in Gamma_e,                                      (ONK1)

machine e does not halt
  => max_(r in R_e)||r(U)-I||_op<delta_e
     implies ||w_e(U)-I||_op<=alpha_e                        (ONK2)
```

for every finite-dimensional unitary tuple `U`.  Then one can effectively
construct a finitely presented non-MF group.

The proof is the same reverse fixed point as
`kleene-halting-mark-collapse-proof`, but the endpoint is easier.  Let `e_*`
be a Kleene fixed point for the machine which enumerates a van Kampen proof of
`w_e=1` in `Gamma_e`.  If it halted, `(ONK1)` would contradict the proof it
just found; hence it does not halt, and completeness of the proof enumeration
gives

```text
w_(e_*)!=1 in Gamma_(e_*).                                   (ONK3)
```

Now `(ONK2)` applies.  If `Gamma_(e_*)` were MF, the local formulation of the
MF property would supply finite-dimensional unitary tuples with relator
operator-norm defect tending to zero while keeping the nontrivial word
`w_(e_*)` at operator-norm distance at least `1` from the identity.  For all
large stages the defect is below `delta_(e_*)`, so `(ONK2)` instead gives

```text
||w_(e_*)(U)-I||_op<=alpha_(e_*)<1,
```

a contradiction.

## Why this is a genuinely weaker compiler target

`(ONK2)` is required only for tuples whose **worst-direction** relator error is
small.  It need not control normalized-HS microstates which are allowed to
corrupt a small-rank computational sector.  Thus the positive-density return,
metapixel amplification, and anti-dilution machinery required by the
hyperlinear route are not part of this theorem's hypotheses.

This does not itself instantiate the compiler.  It records the correct
MF-specific construction target: build a self-referential group computation
whose strategically useful corruption costs a fixed amount in operator norm.
Rank/spectral discreteness may be used here in ways unavailable to the
normalized-HS compiler.

## Finite disjunctive strengthening

The same theorem remains true when the compiler outputs a finite list

```text
w_(e,1),...,w_(e,m_e)
```

and replaces `(ONK1)--(ONK2)` by

```text
e halts    => every w_(e,i) is nontrivial,                  (DONK1)
e nonhalts => defect_op(U)<delta_e
              implies min_i ||w_(e,i)(U)-1||_op<=alpha_e.  (DONK2)
```

Here `m_e` is finite and computable from `e`, and still `alpha_e<1`.
Make the fixed-point machine enumerate van Kampen proofs and halt when it
finds `w_(e,i)=1` for **any** `i`.  If it halted, `(DONK1)` would contradict
the proof just found.  Thus it does not halt, and completeness of proof
enumeration says every mark in its finite list is nontrivial.

It remains to justify simultaneous MF separation; this is slightly stronger
than merely saying each image is nonidentity.  In an injective norm-corona
model, fix one mark `w_i` and a spectral value `lambda_i!=1` of its image.
Some tensor power satisfies

```text
|lambda_i^(k_i)-1|>1,
```

because the closure of the powers of a nontrivial circle element is a
nontrivial compact subgroup of the circle and contains a point at distance
greater than `1` from `1`.  After passing to a subsequence for this mark, the
coordinatewise `k_i`-fold tensor power of the lifted asymptotic
representation separates `w_i` by more than `1`, while its operator-norm
multiplicative defect still tends to zero.  For one requested defect
tolerance, choose one sufficiently late coordinate from each of these
finitely many (possibly different) subsequences and take their direct sum.
The `i`-th block separates `w_i`, and the operator norm of a block sum is the
maximum, so one finite-dimensional tuple simultaneously has

```text
defect_op(U)<delta_e,
||w_(e,i)(U)-1||_op>1>alpha_e  for every i.
```

This contradicts `(DONK2)`.  Therefore a finite universal library together
with disjunctive collapse is enough for non-MF.  Finiteness is essential to
the direct-sum step; this statement does not promote an infinite moving
library to a uniform obstruction.
