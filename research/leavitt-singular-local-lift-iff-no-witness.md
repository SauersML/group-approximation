---
rg: 2
id: leavitt-singular-local-lift-iff-no-witness
kind: claim
title: The Leavitt singular local-lift terminal is equivalent to nonexistence, not a weaker consequence of Calkin support
distinct_from:
  binary-leavitt-near-regular-quotient-is-locally-liftable: that is the universal local-lift statement over hypothetical singular witnesses; this proves that every actual witness would have a nonlocally-liftable quotient, so that universal statement holds exactly when there are no witnesses.
  invariant-free-near-state-is-amenable-regular-cover: that constructs the trace-kernel quotient and identifies it with the reduced algebra; this uses nonamenability and trace descent to determine the lifting polarity of every hypothetical instance, and also records the intervening Calkin quotient.
  amenable-trace-descends-through-locally-liftable-quotient: that is a general one-way trace theorem; this applies it to the Leavitt regular quotient and obtains an equivalence between an open universal lifting assertion and witness nonexistence.
---

**ESTABLISHED (endpoint audit).**  Let

```text
Q=L_(F_2)(1,2)^x
```

and suppose `(H,phi,pi)` is a purely singular invariant free near-state
witness.  Put

```text
A=C^*(pi(Q)),   tau=phi|_A,
I_tau={a:tau(a^*a)=0},   B=A/I_tau ~= C^*_r(Q).          (SLT1)
```

Then the quotient `q:A->B` is **not** locally ucp-split.

Indeed, `tau` is amenable by
`invariant-free-near-state-is-amenable-regular-cover`.  If `q` were locally
ucp-split, `amenable-trace-descends-through-locally-liftable-quotient` would
make the canonical regular trace on `C^*_r(Q)` amenable.  For a discrete
group this is equivalent to amenability of the group.  But `Q` is nonsofic by
`openai-leavitt-unit-nonsofic`, hence nonamenable.  This contradiction proves
the assertion.

Consequently

```text
every singular free near-state cover has locally liftable regular quotient
  iff no singular free near-state cover exists.                       (SLT2)
```

The forward implication is the existing local-lift route.  For the reverse,
the universal assertion is vacuous when no witness exists.  More sharply, if
even one witness exists, the first paragraph says its quotient is a
counterexample to the universal assertion.  Thus
`binary-leavitt-near-regular-quotient-is-locally-liftable` is exactly
equivalent to `binary-leavitt-has-no-purely-singular-free-near-representation`;
it is not an easier terminal unless additional structure proves the lifting
statement by an argument that simultaneously rules out the witness.

**What pure singularity actually supplies.**  Let `K=K(H)` and

```text
J=A cap K,       dot A=A/J subset B(H)/K(H).              (SLT3)
```

Because a purely singular state annihilates the compacts,

```text
J subset I_tau,
A ->> dot A ->> A/I_tau ~= C^*_r(Q),                      (SLT4)
```

and `phi` factors to a state on the Calkin algebra.  Notice the direction:
singularity gives only `J subset I_tau`, not `I_tau subset J`.  Hence the
regular quotient need not embed in the Calkin algebra; it is generally a
further quotient of the concrete Calkin image by `I_tau/J`.

Moreover, at least one arrow in `(SLT4)` is not locally ucp-split.  If both
were, a local section of the second arrow on a finite-dimensional operator
system `E` would have a completely order embedded finite-dimensional image in
`dot A`; locally lifting that image through the first arrow and composing
would locally split `q`, contrary to the first paragraph.

There is no generic Calkin rescue even in the special case `I_tau=J`.
Harris, arXiv:2508.00113, Corollary 5, gives explicit four-dimensional
operator subsystems of the Calkin algebra whose identity maps have no ucp
lift to `B(H)`.  Thus factoring a state through the Calkin algebra carries no
local-lifting theorem.  The special Leavitt relations identify the final
quotient and force its nonlifting polarity if a witness exists; they do not,
by singularity alone, construct a section or a direct contradiction.

DERIVATION
amenable-regular-trace-forces-singular-cover-nonlifting
