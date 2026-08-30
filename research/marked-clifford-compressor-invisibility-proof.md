---
rg: 2
id: marked-clifford-compressor-invisibility-proof
kind: route
title: Compute the Clifford permutation trace, recover Haar spectrum, and invoke proper outerness
target: marked-clifford-compressor-hyperfinite-invisibility
requires:
  - hyperfinite-covariant-obstruction-lemma
artifacts:
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
---

Let `rho:Gamma->U(W)` be a homomorphism into a finite injective von Neumann
algebra with faithful normal trace `tau`.  The `-1` spectral projection

```text
p=(1-rho(w))/2
```

is central in `rho(Gamma)''`.  If `p!=0`, compress to `pWp`, normalize the
trace, and replace `rho` by the compressed representation.  Thus it is enough
to contradict `rho(w)=-1`.

The `2m` represented lamps are pairwise anticommuting self-adjoint
unitaries.  They generate a unital copy of

```text
Cl_(2m)(C)=M_(2^m).
```

Write `C` for this matrix algebra.  For `v in V`, conjugation by `rho(v)`
restricts to the automorphism of `C` which permutes the Clifford generators
by `m` disjoint transpositions.  Choose an implementing unitary `V_v in C`.
The matrix-algebra tensor decomposition of `W` gives

```text
rho(v)=V_v x_v,          x_v in C' intersect W,
tau(rho(v))=tr_(2^m)(V_v) tau(x_v).                    (MCC1)
```

The normalized trace of `V_v` is zero.  Indeed

```text
|tr_(2^m)(V_v)|^2=tr_(2^(2m))(Ad V_v).
```

On the Clifford monomial basis, a monomial is fixed by the permutation
exactly when its support is a union of `j` transposition pairs.  Reversing
each selected anticommuting pair contributes one minus sign, so

```text
tr_(2^(2m))(Ad V_v)
 =sum_(j=0)^m binomial(m,j)(-1)^j
 =(1-1)^m=0.                                             (MCC2)
```

Equations `(MCC1)`--`(MCC2)` give `tau(rho(v))=0` for every `v in V`.
Trace invariance under conjugacy and hypothesis 3 therefore imply

```text
tau(rho(n))=0                  (n in N\{e}).             (MCC3)
```

Hence `rho|N` has the regular character.  In particular it is faithful and

```text
rho(N)'' = L(N)=L_infinity(N_hat,Haar).                 (MCC4)
```

Conjugation by `rho(h)` on `(MCC4)` is precisely the dual action of `h`.
For an abelian von Neumann algebra, an intertwiner

```text
x a=alpha_h(a)x                 (a in L_infinity(N_hat))
```

is supported on the fixed-point set of the underlying transformation:
apply the identity to indicator functions from a countable generating
sigma-algebra.  Hypothesis 4 makes that support null for every `h!=e`.
Thus the `H`-action on `rho(N)''` is properly outer.

Apply `hyperfinite-covariant-obstruction-lemma` to the represented subgroup
`N semidirect H`.  Proper outerness makes `rho(H)''` a copy of `L(H)` inside
the finite injective algebra `W`; the trace-preserving expectation would
make `L(H)` injective, forcing `H` amenable.  This contradicts the
hypothesis.  Therefore `p=0` and `rho(w)=1`.
