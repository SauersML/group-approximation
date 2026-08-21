---
rg: 2
id: uniform-clock-reflection-block-encodes-game-hamiltonian
kind: claim
title: One controlled flag reflection has the game Hamiltonian as its exact corner Dirichlet form
distinct_from:
  two-copy-bcs-game-hamiltonian-dominates-fanizza-signal: that constructs the positive rational losing Hamiltonian; this packages its entire finite sum into one algebraic unitary reflection.
---

Let

```text
H=sum_(j=1)^M (1/M)L_j                                (UCR1)
```

be a uniform average of projections in a unital star algebra.  Rational
weights reduce to `(UCR1)` by duplicating terms.  On the finite clock and one
flag qubit define

```text
C=sum_(j=1)^M e_(jj) tensor
  ((1-L_j) tensor 1 + L_j tensor X),                  (UCR2)
```

where `X` flips the flag.  Then `C=C^*=C^(-1)`.  Let

```text
q_s=(1/M) sum_(i,j)e_(ij),
q_0=(1+Z)/2,
Q=q_s tensor q_0.                                     (UCR3)
```

Under the natural identification `Q(H^M tensor C^2)` with the original
space,

```text
Q(1-Re C)Q = H tensor Q.                              (UCR4)
```

## Proof

Each summand in `(UCR2)` is block diagonal over the system projection
`L_j` and equals either the identity or the flag flip.  Hence it is a
self-adjoint unitary, and the clock blocks make their sum a self-adjoint
unitary.  Moreover

```text
<0|((1-L_j) tensor 1+L_j tensor X)|0>=1-L_j.
```

Averaging the diagonal clock blocks in the uniform clock vector gives
`1-H`.  Therefore the compression of `1-C` is exactly `H`, proving `(UCR4)`.

All entries are rational finite group-algebra expressions whenever the
`L_j` are.  For the Fanizza two-copy Hamiltonian this produces one explicit
finite-support reflection `V_m` satisfying

```text
Q D_R Q <= C_m Q(1-Re V_m)Q                          (UCR5)
```

in every nonmember representation, where `C_m` is the Fanizza soundness
constant.

This closes aggregation completely.  It does not promote `C_m` to an
ordinary group word, nor make its selected clock/flag corner a fixed
finite-matrix carrier.  Those two requirements are exactly the remaining
wandering Hecke promotion.
