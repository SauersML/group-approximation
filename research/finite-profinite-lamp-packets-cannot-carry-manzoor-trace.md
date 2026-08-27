---
rg: 2
id: finite-profinite-lamp-packets-cannot-carry-manzoor-trace
kind: claim
title: Finite and profinite lamp packets cannot carry Manzoor's non-co-hyperlinear trace
distinct_from:
  random-coset-lamp-correlations-realize-every-irs-character: that realizes every IRS value by a direct integral of subgroup-dependent infinite coset lamps; this rules out replacing that measurable field by finite, countably mixed, or profinite permutation packets when a multiplicative trace realization is required.
  haar-algebraic-actions-have-permutation-koopman-spectrum: that gives reciprocal-index restrictions for Haar algebraic stabilizers; this uses Connes embeddability of finite permutation characters and applies to arbitrary finite/profinite stabilizer packets.
  manzoor-separation-does-not-specify-haar-cylinders: that says the published witness has no explicit cylinder oracle; this needs no cylinder values and uses only the established non-CE character.
---

Let `Gamma` act on a finite set `X`.  Its stabilizer IRS under a uniform
random point has character

```text
phi_X(g)=|Fix_X(g)|/|X|,                                (FPL1)
```

which is the normalized character of the finite-dimensional permutation
representation on `C^X`.  The lamp formula also has an exact finite block
form.  In `M_|X|(L((directSum_X C_2) semidirect Gamma))`, put

```text
A=diag(a_x)_(x in X),       U_g=diag(g)_(x in X).
```

Then normalized matrix/group trace gives

```text
tau(A U_g A U_g^*)=phi_X(g).                            (FPL2)
```

Any countable probability mixture `sum_n t_n phi_(X_n)` is the trace of the
block-diagonal direct sum of these finite-dimensional permutation
representations.  Its GNS algebra is hyperfinite, hence Connes embeddable.
Likewise, if a probability action is an inverse limit of finite actions, then

```text
mu(Fix(g))=lim_n |Fix_(X_n)(g)|/|X_n|                  (FPL3)
```

by continuity from above of the nested fixed-point cylinders.  Its character
is a pointwise limit of finite-dimensional characters and is again
Connes embeddable/co-hyperlinear.

Therefore neither a countable disjoint union with atomic packet weights nor
a nonatomic profinite inverse-limit packet can realize Manzoor's IRS
**trace**, whose GNS algebra is non-Connes-embeddable.  If a proposed packet
construction puts actual multiplicative unitaries with character `phi_mu`
in a matrix ultraproduct, it has asserted exactly the co-hyperlinearity that
Manzoor disproves.

There are two apparent evasions, neither a solution.

- A countable mixture of arbitrary infinite coset subgroups may already use
  a non-co-hyperlinear component; then the hard trace has merely been inserted
  into one packet, not constructed from finite/profinite data.
- Matching only the nonlinear lamp correlations `(FPL2)` need not make
  `phi_mu` the trace of a representation, as
  `random-coset-lamp-correlations-realize-every-irs-character` proves.

Thus finite packets are decisively fenced.  Exact realization of the
nonatomic IRS law in one ordinary group factor is not a limit-of-packets
problem; it is the group-factor/algebraic-envelope problem itself.

