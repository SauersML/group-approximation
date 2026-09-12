---
rg: 2
id: stw07-primitive-quotient-traces-separate-proof
kind: route
title: Pull faithful MF traces back from primitive quotients and separate every positive element
target: stw07-primitive-mf-traces-force-quasidiagonality
requires:
  - stw09-jointly-faithful-mf-traces-force-mf
---

For each primitive ideal `P` choose a faithful MF tracial state `tau_P` on
`A/P`, and let `q_P:A->A/P` be the quotient map.  The pullback

```text
sigma_P=tau_P o q_P
```

is an MF tracial state on `A`: compose any asymptotically multiplicative
matrix coordinates for `tau_P` with `q_P`.  No faithfulness survives or is
needed on `A`.

The family `(sigma_P)` is jointly faithful.  Indeed, if `0!=a in A`, choose
an irreducible representation `pi` with `pi(a)!=0` and put `P=ker(pi)`.
Then `q_P(a*a)` is nonzero and positive.  Faithfulness of `tau_P` gives

```text
sigma_P(a*a)=tau_P(q_P(a*a))>0.                       (PQ1)
```

The separation theorem
`stw09-jointly-faithful-mf-traces-force-mf` now makes `A` MF.  If `A` is
nuclear, the nuclear-MF characterization makes it quasidiagonal.

For the final assertion, suppose every primitive quotient carries a faithful
tracial state and satisfies the UCT.  Each `A/P` is separable, unital and
nuclear.  Its faithful trace is amenable, and the UCT quasidiagonality theorem
makes it a quasidiagonal, hence MF, trace.  Thus every primitive quotient has
the trace required in the first paragraph, and `(PQ1)` completes the proof.

**Trust boundary.**  Neither stable finiteness of `A` nor stable finiteness of
one primitive quotient is asserted to supply a faithful trace on that
quotient.  Faithfulness is part of the fibrewise hypothesis, and no
continuity or measurable selection of the chosen traces is used.
