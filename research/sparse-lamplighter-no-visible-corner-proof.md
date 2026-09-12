---
rg: 2
id: sparse-lamplighter-no-visible-corner-proof
kind: route
title: Shift-orbit averaging erases a rank-one lamp in every commuting corner
target: sparse-lamplighter-corona-has-no-visible-corner
requires: []
artifacts:
  - research/artifacts/weak-mf-hs-profile-audit-2026-08-30.md
---

## Direct proof

### 1. The faithful corona representation

Let `e_0,...,e_(n-1)` be the standard basis of `C^n`, let `S_n e_j` be
`e_(j+1 mod n)`, and put

```text
A_n = I_n-2 |e_0><e_0|.
```

The assignments `s |-> S_n`, `a |-> A_n`, together with

```text
s^j a s^(-j) |-> I_n-2 |e_(j mod n)><e_(j mod n)|,
```

define an exact representation `u_n:L->U(n)` through the finite cyclic
lamplighter quotient.  They therefore define a homomorphism

```text
u:L->U(Q),       u(x)=[(u_n(x))_n].
```

It is injective.  Write a nonidentity element as `(f,k)`, where `f` has
finite support and `k in Z`.  If `k=0`, then for all sufficiently large `n`
the nonempty support of `f` has no collisions modulo `n`; hence `u_n(f,0)`
has a diagonal entry `-1` and

```text
||u_n(f,0)-I||_op=2.
```

If `k!=0`, then for `n>|k|` the underlying monomial matrix moves every basis
vector by `k mod n`.  Thus for every `j`,

```text
||(u_n(f,k)-I)e_j||=sqrt(2),
```

and `||u_n(f,k)-I||_op>=sqrt(2)`.  Therefore no nonidentity element dies in
the norm corona.

### 2. Every shift-invariant corner loses the lamp

Let `P in u(L)' cap Q` be a nonzero projection.  Lift it to projections
`q_n in M_n`, put `I_q={n:q_n!=0}`, and write, for `n in I_q`,

```text
r_n=rank(q_n)>=1,
delta_n=||[q_n,S_n]||_op -> 0,
t_(n,j)=<q_n e_j,e_j> in [0,1].
```

For each fixed `j`, telescoping gives

```text
||S_n^(-j) q_n S_n^j-q_n||_op <= j delta_n,
```

and hence

```text
|t_(n,j)-t_(n,0)| <= j delta_n.                       (LC2)
```

Fix `K>=1`.  For `n>K`, the vectors `e_0,...,e_(K-1)` are distinct, so

```text
r_n = Tr(q_n)
    >= sum_(j=0)^(K-1) t_(n,j)
    >= K t_(n,0)-delta_n K(K-1)/2.
```

Since `r_n>=1`, division by `K r_n` yields the rank-uniform estimate

```text
t_(n,0)/r_n <= 1/K + delta_n (K-1)/2.                 (LC3)
```

The set `I_q` is infinite because `P!=0`.  First let `n->infinity` through
`I_q` and then let `K->infinity`; `(LC3)` proves

```text
t_(n,0)/r_n -> 0.                                    (LC4)
```

Finally, using `A_n=I_n-2|e_0><e_0|` and cyclicity of the ordinary matrix
trace,

```text
tr_(r_n)(q_n A_n q_n)
 = Tr(q_n A_n q_n)/r_n
 = 1-2 t_(n,0)/r_n -> 1.                             (LC5)
```

The expression is real, so `(LC5)` is `(LC1)` along `I_q`.  This argument
applies to every projection lift separately.  Moreover
`q_n A_n q_n` is asymptotically unitary in the corner because `P` commutes
with `u(a)` in `Q`; polar decomposition gives corner unitaries `w_n` with
`||w_n-q_n A_n q_n||_op->0`.  Their normalized traces therefore have the
same limit.  End proof.

## Quantifier boundary

Only commutation with the represented shift was used.  Thus the obstruction
is stronger than failure of the naive spectral projection of `u(a)`: every
projection in the full relative commutant `u(L)' cap Q` is trace-blind to
the lamp.  On the other hand, the conclusion concerns this one realization.
Finite regular representations of finite lamplighter quotients give a
different faithful weak-MF realization with `tr(a)=0`, as residual finiteness
requires.
