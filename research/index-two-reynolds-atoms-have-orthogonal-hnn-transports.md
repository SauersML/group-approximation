---
rg: 2
id: index-two-reynolds-atoms-have-orthogonal-hnn-transports
kind: claim
title: HNN transport of an index-two pair carries its Reynolds atom to an orthogonal character atom
distinct_from:
  central-sign-assignment-atom-is-index-two-reynolds-surplus: That identifies one assignment atom as a Reynolds difference and obtains one exit projection; this transports the difference itself between two marked finite pairs.
  subgroup-hecke-hnn-is-a-regular-safe-rank-actuator: That transports one subgroup fixed space into another; this conjugates both levels of an index-two flag and subtracts them.
  finite-tag-covariance-cannot-compress-eight-slice-orbit: That rules out compressing excess mass by exact finite tags; this constructs only equal-capacity orthogonal atom destinations and asserts no supercritical compression.
---

Let `H<C` and `H'<C'` be index-two inclusions of finite groups and let

```text
phi:C -> C',              phi(H)=H'                    (ITH1)
```

be an isomorphism of marked pairs.  In the HNN extension with stable letter
`u` satisfying

```text
u c u^(-1)=phi(c)                  (c in C),            (ITH2)
```

put

```text
A=e_H-e_C,                 A'=e_(H')-e_(C').           (ITH3)
```

Then `A,A'` are projections and, in the complex group algebra,

```text
u A u^(-1)=A'.                                             (ITH4)
```

Thus an assignment atom supplied by
`central-sign-assignment-atom-is-index-two-reynolds-surplus` can be moved by
ordinary finite-group covariance relations without naming its nonlinear
spectral reflection.

The normalized-HS estimate is dimension independent.  For unitary matrices
`U`, exact finite-group representations `pi,pi'`, and

```text
epsilon_c=||U pi(c) U^*-pi'(phi(c))||_2,
```

one has

```text
||U pi(A)U^*-pi'(A')||_2
 <= |H|^(-1)sum_(h in H) epsilon_h
    +|C|^(-1)sum_(c in C) epsilon_c.                  (ITH5)
```

Fixed-finite-group flexible exactification adds only its standard vanishing
discarded mass.

## Orthogonal destination packet

Take `T=(C_2)^r`.  For every nontrivial character `chi in hat(T)`, put

```text
D_chi=e_(ker chi)-e_T.                                  (ITH6)
```

Fourier decomposition of `C[T]` shows that `D_chi` is exactly the minimal
central projection for `chi`.  Hence distinct nontrivial characters give

```text
D_chi D_psi=0                    (chi!=psi),
sum_(chi in I) D_chi <=1-e_T                              (ITH7)
```

for every finite set `I` of distinct characters.  After padding the source
pair by a common elementary-abelian factor, it is isomorphic to
`ker(chi)<T`; applying `(ITH4)` gives a finite family of ordinary HNN rows
which sends separately named Reynolds assignment atoms to pairwise
orthogonal target atoms.

## Firewall and exact scope

This is a **capacity-preserving router**, not the missing matrix-only
capacity theorem.  In the canonical regular trace

```text
tau(D_chi)=1/|T|,                                        (ITH8)
```

and conjugacy preserves that trace.  Therefore literal pair-HNN rows cannot
route a source family of larger total Plancherel mass into fewer target
characters while preserving the finite packet.  Such a claim would
contradict `canonical-types-extend-every-finite-bass-serre-actor` and the
regular trace.

The useful interface is narrower: once a genuinely shared-BCS,
finite-matrix-only argument has selected a family whose total active mass is
not trace-functorial, `(ITH4)--(ITH7)` provide its local atom transport and
orthogonality with fixed constants.  The unresolved selection/capacity step
remains `typewise-schur-tail-partition-compiler` (or, on the first-hit lane,
`central-sign-reynolds-first-hit-compiler`).
