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
