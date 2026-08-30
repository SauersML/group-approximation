---
rg: 2
id: finite-packet-compressor-invisibility-proof
kind: route
title: Split moved and fixed finite-packet blocks and spread zero Fourier coefficients
target: finite-packet-compressor-hyperfinite-invisibility
requires:
  - hyperfinite-covariant-obstruction-lemma
---

Let `rho:Gamma->U(W)` be a homomorphism into a finite injective von Neumann
algebra with faithful normal trace `tau`.  The projection

```text
p=(1-rho(w))/2
```

is central in `rho(Gamma)''`.  If it is nonzero, pass to the finite injective
corner `pWp`, normalize its trace, and replace `rho` by the compression.
Thus it suffices to contradict `rho(w)=-1`.

The representation of `C*(K)` factors through the negative block

```text
A_-=e_-C*(K)e_- isomorphic to directSum_(j in J) M_(d_j).
```

Let `z_j` be its minimal central projections and put `q_j=rho(z_j)`, allowing
`q_j=0` when the representation kills that summand.  The nonzero `q_j` are
orthogonal and sum to one.  If `sigma_v` is the permutation of the summands
induced by `v`, then

```text
rho(v) q_j rho(v)^*=q_(sigma_v(j)).                    (FP0)
```

When `sigma_v(j)!=j`, traciality and `(FP0)` give

```text
tau(q_j rho(v))=tau(q_j rho(v) q_j)=0;
```

the first equality follows because the complementary corner has zero trace
against `q_j`, and the second because
`q_j rho(v) q_j=q_j q_(sigma_v(j)) rho(v)=0`.

Now suppose `sigma_v(j)=j` and `q_j!=0`.  In the finite corner `q_jWq_j`,
the surviving representation of the simple summand `M_(d_j)` is unital and
faithful.  The standard matrix-corner decomposition gives

```text
q_j W q_j isomorphic to M_(d_j) tensorbar W_j.
```

The unitary `q_j rho(v)` normalizes the matrix factor.  If `U_(v,j)`
implements the prescribed automorphism on it, then

```text
q_j rho(v)=U_(v,j) x_(v,j),
x_(v,j) in M_(d_j)' intersect q_j W q_j.
```

Consequently

```text
tau(q_j rho(v))=0.
```

Summing over the finitely many central summands proves

```text
tau(rho(v))=0.                                         (FP1)
```

Trace invariance under conjugacy and hypothesis 3 spread `(FP1)` to

```text
tau(rho(n))=0                   (n in N\{e}).           (FP2)
```

Thus `rho|N` has the regular character and

```text
rho(N)'' isomorphic to L(N)=L_infinity(N_hat,Haar).    (FP3)
```

For `h in H`, the trace-preserving expectation of `rho(h)` onto `(FP3)` is
an intertwiner between the identity and the dual action of `h`.  Such an
intertwiner in an abelian von Neumann algebra is supported on the fixed-point
set.  Hypothesis 4 therefore makes the represented `H`-action properly
outer for every `h!=e`.

The hyperfinite covariant obstruction lemma now puts a copy of `L(H)` in
the finite injective algebra `W`.  Its trace-preserving expectation would
make `L(H)` injective, forcing `H` to be amenable, contrary to hypothesis.
Hence `p=0` and `rho(w)=1`.
