---
rg: 2
id: stw09-finite-direct-sum-mf-separation-proof
kind: route
title: Direct-sum finitely many trace coordinates that norm a prescribed packet
target: stw09-jointly-faithful-mf-traces-force-mf
requires: []
---

For each `sigma in T`, choose MF-trace coordinates

```text
phi_(sigma,n): A -> M_(d(sigma,n)).
```

Thus the maps are pointwise bounded and asymptotically linear,
star-preserving and multiplicative in operator norm, while

```text
tr(phi_(sigma,n)(b)) -> sigma(b)                              (JMF2)
```

for every `b in A`.  They induce a star homomorphism

```text
Phi_sigma:A -> product_n M_(d(sigma,n)) / directSum_n M_(d(sigma,n)).
```

The first key point is that positive trace detection implies norm-corona
detection.  If `Phi_sigma(a)=0`, then `||phi_(sigma,n)(a)|| -> 0`.
Asymptotic star preservation and multiplicativity give

```text
||phi_(sigma,n)(a* a)
       - phi_(sigma,n)(a)^* phi_(sigma,n)(a)|| -> 0.
```

Hence `||phi_(sigma,n)(a* a)|| -> 0`; normalized matrix traces and `(JMF2)`
then give `sigma(a* a)=0`.  The contrapositive and `(JMF1)` show that the
product homomorphism

```text
Phi = product_(sigma in T) Phi_sigma
```

is injective, hence isometric.

Here is the finite-coordinate argument, included so that injectivity of an
arbitrary product is not being used as a hidden sequential embedding.  Fix a
finite packet `F` in `A` and `epsilon>0`.  For every `x in F`, isometry of
`Phi` supplies `sigma_x in T` such that

```text
||Phi_(sigma_x)(x)|| > ||x||-epsilon.                         (JMF3)
```

The norm in a matrix sequence quotient is the limsup of the coordinate
norms.  For each `x`, choose a sufficiently late coordinate `n_x` which
satisfies `(JMF3)` up to another `epsilon`, has upper norm bound
`||phi_(sigma_x,n_x)(y)|| <= ||y||+epsilon` for every `y in F`, and has all
linearity, star and multiplication defects requested on `F` below
`epsilon`.  This is possible because the defects converge to zero and the
upper limsup is bounded by the norm of `y`, while the lower inequality for
the distinguished `x` occurs arbitrarily far out.

Take the finite direct sum

```text
Psi_F = directSum_(x in F) phi_(sigma_x,n_x):A -> M_D.        (JMF4)
```

Every defect of `(JMF4)` is the maximum of the corresponding block defects,
and the block indexed by `x` gives

```text
||x||-2 epsilon < ||Psi_F(x)|| <= ||x||+epsilon.
```

Therefore arbitrarily accurate approximately multiplicative and
approximately isometric matrix models exist on every finite packet.
Separability and the usual diagonal exhaustion give one asymptotically
isometric MF coordinate sequence for `A`.  This proves that `A` is MF.

If `A` is nuclear, the Blackadar--Kirchberg characterization of NF algebras
(nuclear plus MF if and only if nuclear plus quasidiagonal) now makes `A`
quasidiagonal.  This last standard theorem is the only literature input; no
UCT or promotion of an amenable trace to a quasidiagonal trace is used.
