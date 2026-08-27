---
rg: 2
id: full-q-quarter-stabilizer-cross-kernel-proof
kind: route
title: Induce the natural stabilizer permutation type and compute the native cross kernel
target: full-q-quarter-stabilizer-profile-has-cross-kernel
requires:
  - b2-b3-pair-full-hecke-four-native-sectors
  - full-moving-hecke-packet-retains-q-kernel-profile
---

Take the pairing-one base character `(a,b)=(e_0^*,e_0)`.  Its stabilizer in
`GL_5(F_2)` fixes both `e_0` and `e_0^*`, hence is the block copy

```text
H={1} times GL_4(F_2).                                  (1)
```

Let `H` act on the `15` nonzero vectors of the fixed four-space.  This
action is two-transitive: after fixing one nonzero vector, every different
nonzero vector is an independent second vector, and the stabilizer is
transitive on those choices.  Hence its complex permutation representation
is the orthogonal sum of the trivial representation and an irreducible
`14`-dimensional zero-sum representation.

First induce the full permutation representation.  Choose,
for every one of the `496` pairing-one characters `omega`, a transporter
`g_omega` from the base character.  The standard induced monomial action is

```text
g:(omega,u) |->
  (g omega, (g_(g omega)^(-1) g g_omega)u),             (2)
```

where the parenthesized factor belongs to `H`.  Formula `(2)` is independent
of any canonical trace choice and gives an exact representation of the full
finite parabolic quotient.

Lift the ten signed `L_0` generators to `(2)`, using their ordinary radical
characters for the diagonal phases.  Signed-component propagation gives

```text
rank e_(L_0,lambda_0)=132.                              (3)
```

The literal operators

```text
r=x_(u_2,u_0)(1),      l(a,b)=(-1)^(b_3),
J_1=(u_1 u_2),         J_2=(u_2 u_3)                   (4)
```

act by the same induced rule `(2)`.  Cutting the `l=+1` components and then
the `r=+1` component pairs yields `33` mutually orthogonal signed-component
vectors spanning `F`.

Their squared norms, in the deterministic component order used by the
audit, are

```text
(8,4,8,4,4,4,8,4,8,4,4,8,4,8,4,4,4,
 8,4,8,4,4,8,4,8,4,4,4,8,4,8,4,4).                   (5)
```

Directly applying the two permutations in `(4)` gives an integer cross
matrix of rank `27`.  After dividing its entries by the square roots of the
corresponding norms in `(5)`, the sum of squared entries is exactly `6`.
The full permutation fiber gives

```text
rank(Q)=132,       rank(F)=33,       rank(T_1^*T_2)=27,
Tr_F(T_1^*T_2T_2^*T_1)=6.                              (6)
```

The trivial fiber summand is exactly the scalar pairing-one profile of
`full-q-quarter-adjacent-profiles-have-half-cross`; it has ranks
`12,3,3` and energy `3/4`.  All group-algebra operators in `(3)--(4)`
preserve the orthogonal stabilizer decomposition, so ranks and squared
Hilbert--Schmidt norms add across it.  Subtracting the trivial summand from
`(6)` gives

```text
rank(Q)=120,       rank(F)=30,       rank(T_1^*T_2)=24,
Tr_F(T_1^*T_2T_2^*T_1)=6-3/4=21/4.                    (7)
```

Dividing the last value by `30` gives `7/40`, proving
`(QSK2)--(QSK3)` on the irreducible nontrivial stabilizer profile.

`experiments/full_q_quarter_stabilizer_permutation_audit.py` constructs the
`496` transporters by breadth-first traversal, checks every cocycle in
`(2)` fixes the base pair, propagates the full signed packet on all `7440`
states, computes the ranks and normalized energy by exact integer
arithmetic, and performs the exact subtraction `(6)--(7)`.  It was run
with Python 3.11 through the MSI wrapper and
completed in under five seconds.
