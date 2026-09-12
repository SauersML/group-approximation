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
algebra with faithful normal trace `tau`.  For every `q`-th root `lambda`,
the spectral projection

```text
p_lambda=q^(-1) sum_(k=0)^(q-1) lambda^(-k) rho(w)^k
```

is central in `rho(Gamma)''`.  Fix `lambda!=1`.  If `p_lambda` is nonzero,
pass to the finite injective corner `p_lambda W p_lambda`, normalize its
trace, and replace `rho` by the compression.  Thus it suffices to contradict
`rho(w)=lambda`.

The representation of `C*(K_lambda)` factors through the corresponding
central-character block

```text
A_lambda=e_lambda C*(K_lambda)e_lambda
  isomorphic to directSum_(j in J_lambda) M_(d_(lambda,j)).
```

Let `z_j` be its minimal central projections and put `q_j=rho(z_j)`, allowing
`q_j=0` when the representation kills that summand.  The nonzero `q_j` are
orthogonal and sum to one.  For `v in V_lambda`, let `sigma_v` be the
permutation of the summands induced by `v`.  Then

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
the surviving representation of the simple summand `M_(d_(lambda,j))` is unital and
faithful.  The standard matrix-corner decomposition gives

```text
q_j W q_j isomorphic to M_(d_(lambda,j)) tensorbar W_j.
```

The unitary `q_j rho(v)` normalizes the matrix factor.  If `U_(v,j)`
implements the prescribed automorphism on it, then

```text
q_j rho(v)=U_(v,j) x_(v,j),
x_(v,j) in M_(d_(lambda,j))' intersect q_j W q_j.
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
Hence `p_lambda=0`.  This holds for every `lambda!=1`, while all the spectral
projections sum to one.  Therefore `rho(w)=1`.
