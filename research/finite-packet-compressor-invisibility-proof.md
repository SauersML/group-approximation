---
rg: 2
id: finite-packet-compressor-invisibility-proof
kind: route
title: Factor the trace over the unique finite packet and spread zero Fourier coefficients
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

The representation of `C*(K)` then factors through the negative block
`e_-C*(K)e_- isomorphic to M_d`.  It is unital on that block and therefore
faithful, so its range is a unital matrix subalgebra `C isomorphic to M_d`
of `W`.  The standard matrix-corner decomposition gives

```text
W isomorphic to M_d tensorbar W_0,
tau=tr_d tensor tau_0.
```

For `v in V`, `rho(v)` normalizes `C` and induces the prescribed
automorphism.  If `U_v in C` implements that automorphism, then

```text
rho(v)=U_v x_v,                 x_v in C' intersect W.
```

Consequently

```text
tau(rho(v))=tr_d(U_v) tau_0(x_v)=0.                    (FP1)
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
