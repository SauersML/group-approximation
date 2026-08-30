---
rg: 2
id: prime-heisenberg-compressor-hyperfinite-invisibility
kind: claim
title: A prime Heisenberg phase certificate and an abelian compressor force hyperfinite mark invisibility
distinct_from:
  marked-clifford-compressor-hyperfinite-invisibility: that treats a central involution through signed permutations of anticommuting Clifford generators; this treats a central mark of arbitrary prime order through the fixed-space character of a finite Heisenberg normalizer.
  hyperfinite-covariant-obstruction-lemma: that starts from proper outerness of a represented semidirect-product action; this supplies proper outerness from finite Heisenberg phase data and conjugacy compression.
artifacts:
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
---

Let `p` be prime and let `Gamma` have a central element `w` of order `p`.
Suppose `Gamma` contains a finite Heisenberg subgroup

```text
H_(p,m)=<w,x_1,...,x_m,y_1,...,y_m>,                  (PH0)
```

where `m>=1`, all displayed generators have order `p`,
`[x_i,y_j]=w^(delta_ij)`, and all other pairs of displayed noncentral
generators commute.  (For `p=2`, products such as `x_i y_i` may have order
four, as the relations require.)  For `a=(u,v) in F_p^(2m)`, put

```text
d_a=x_1^(u_1)...x_m^(u_m)y_1^(v_1)...y_m^(v_m).
```

Assume that `Gamma` also contains `B=N semidirect K`, where `N` is
countable abelian and `K` is nonamenable, and a set `V subset Gamma` with
the following properties.

1. Every `g in V` normalizes `H_(p,m)` and fixes `w`.  Thus, for a linear
   symplectic map `S_g` of `F_p^(2m)` and a function
   `q_g:F_p^(2m)->F_p`,

   ```text
   g d_a g^(-1)=w^(q_g(a)) d_(S_g a).                 (PH1)
   ```

   The restriction of `q_g` to `Fix(S_g)` is a nonzero linear functional.
2. Every `n in N\{e}` is conjugate in `Gamma` to an element of `V`.
3. For every `k in K\{e}`, the fixed-point set of the dual action of `k`
   on `N_hat` has Haar measure zero.

Then every homomorphism from `Gamma` to the unitary group of a finite
injective von Neumann algebra kills `w`.

The finite certificate in `(PH1)` is exact.  If `U_g` implements the
normalizer on the unique `p^m`-dimensional representation with
`w=exp(2 pi i r/p)`, `r!=0`, then

```text
|Tr(U_g)|^2
   = sum_(a in Fix(S_g)) exp(2 pi i r q_g(a)/p)=0.     (PH2)
```

Thus a nontrivial additive phase on the fixed subspace replaces the signed
cycle obstruction in the Clifford theorem.  The result applies to every
prime-order central mark and uses neither property `(T)` nor character
classification.
