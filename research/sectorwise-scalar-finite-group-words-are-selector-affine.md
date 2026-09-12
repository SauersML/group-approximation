---
rg: 2
id: sectorwise-scalar-finite-group-words-are-selector-affine
kind: claim
title: A finite-group word scalar on every marked selector sector is itself a selector word
distinct_from:
  finite-selector-gadget-induction-barrier: that uses induction to show every compatible selector character survives in some representation; this classifies literal group words whose scalar is determined by the selector character across all marked irreducibles.
  schur-rank-output-is-not-a-scalar-selector: that rules out reading the Schur rank bit from the original packet generators; this applies to every finite overgroup and even to packets with one simple block per selector sector.
  boolean-predicate-central-phase-word: that constructs selected assignment-indexed irreducible models with a desired phase; this proves such a selected family cannot make the phase selector-sound in all irreducibles of a finite gadget unless the predicate is affine.
---

Let `H` be a finite group and let

```text
D=<J,z_1,...,z_k> isomorphic to (C_2)^(k+1)             (SSW1)
```

be central in `H`.  Put `p_-=(1-J)/2`.  Let `w in H`.  Assume that for every
irreducible representation `pi` with `pi(J)=-I`, the operator `pi(w)` is a
scalar, and that this scalar depends only on the restriction of `pi` to `D`.
Then

```text
w in D.                                                  (SSW2)
```

Consequently, if those scalars lie in `{+1,-1}``, their value on the selector
sector `z_i=(-1)^(x_i)` is an affine Boolean phase

```text
pi_x(w)=(-1)^(c+sum_i a_i x_i).                         (SSW3)
```

To prove the theorem, let `p_chi` be the primitive character projections of
`C[D]` with `chi(J)=-1`.  The hypothesis and semisimplicity imply that for
some scalars `lambda_chi`,

```text
p_- w=sum_(chi(J)=-1) lambda_chi p_chi in p_- C[D].     (SSW4)
```

Thus `p_-w=p_-a` for some `a in C[D]`.  Multiplying by two gives

```text
w-Jw=a-Ja.                                              (SSW5)
```

The right side is supported on the group-basis subset `D`.  If `w` were not
in `D`, then `w` and `Jw` would be two distinct basis elements outside `D`,
and their coefficients `+1,-1` in the left side could not cancel against the
right side.  Hence `w in D`, proving `(SSW2)`; `(SSW3)` is evaluation of an
elementary-abelian character.

This closes the “unique sector” loophole.  In particular, modifying the full
`V_4` radical packet so that every selector sector is one full matrix block
cannot turn a group word into `(-1)^(f(x))` for nonlinear `f`.  The Schur--
Clifford nonlinearity must remain in representation dimension, restriction
multiplicity, or an explicit group-algebra density/projection, and the global
return must transport one of those non-scalar objects.

