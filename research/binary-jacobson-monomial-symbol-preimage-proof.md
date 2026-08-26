---
rg: 2
id: binary-jacobson-monomial-symbol-preimage-proof
kind: route
title: Extend the finitary kernel by the virtually abelian Laurent monomial group and cross the boundary with one raw root
target: binary-jacobson-monomial-symbol-preimage-is-marked-mf
requires:
  - binary-jacobson-elementary-mark-is-finite-quotient-invisible
  - amenable-implies-operator-mf
---

By `binary-jacobson-finitary-kernel-proof`, the symbol map has exact sequence

```text
1 -> L -> E -> EL_5(A) -> 1,
L=GL_fin(N x {1,...,5},F_2),
A=F_2[z,z^(-1)].                                      (1)
```

The marked root `z_Q=x_13(Q)` is a nonidentity element of `L`.

## The monomial symbol group is virtually abelian

Every determinant-one monomial matrix over `A` has a unique permutation
part and a diagonal part

```text
diag(z^(n_1),...,z^(n_5)),             sum_i n_i=0.     (2)
```

In characteristic two the permutation signs disappear.  Constant Weyl
words give all permutation matrices, and the usual elementary torus words

```text
h_ij(u)=w_ij(u)w_ij(-1),               u=z^n,           (3)
```

give the balanced diagonal matrices.  Hence this monomial group lies in
`EL_5(A)` and fits into

```text
1 -> Z^4 -> M -> Sym(5) -> 1.                           (4)
```

It is therefore virtually abelian and amenable.

Taking the inverse image in `(1)` gives

```text
1 -> L -> K -> M -> 1.                                  (5)
```

The group `L` is locally finite, hence amenable.  Amenability is closed under
extensions, so `K` is countable amenable.  The established literature input
`amenable-implies-operator-mf` gives an injective norm-corona representation
of `K`.  Since `z_Q` is a nonidentity element of `L<=K`, this representation
retains it.  If `Ktilde` is the inverse image of `K` in `St_5(J)`, compose

```text
Ktilde -> K -> U(Q_d).                                  (6)
```

The Steinberg root `x_13(Q)` maps to `z_Q`, so `(6)` is the asserted marked
subsystem model.

## One raw Laurent root generates past the firewall

Fix `i!=j` and let `H=<K,x_ij(S)>`.  Its symbol contains `M` and
`x_ij(z)`.  For any integer `n`, choose a third index `k` and the balanced
diagonal monomial

```text
d_n=diag(1,...,z^(n-1) at i,...,z^(1-n) at k,...,1).
```

Because `j` is different from `i,k`, conjugation gives

```text
d_n x_ij(z) d_n^(-1)=x_ij(z^n).                         (7)
```

Constant Weyl elements in `M` move `(i,j)` to every ordered pair `(a,b)`.
Thus `mu(H)` contains `x_ab(z^n)` for all `a!=b` and `n in Z`.  Root
additivity now gives

```text
x_ab(sum_(n in F) z^n)=prod_(n in F) x_ab(z^n)           (8)
```

for every finite set `F`; these are all Laurent coefficients over `F_2`.
Consequently

```text
mu(H)=EL_5(A).                                          (9)
```

But `ker(mu)=L<=K<=H`.  Given `g in E`, choose `h in H` with
`mu(h)=mu(g)` using `(9)`; then `gh^(-1) in L<=H`, so `g in H`.  This proves
`<K,x_ij(S)>=E`.  Replacing `z` by `z^(-1)` proves the identical statement
for `x_ij(T)`.

The argument establishes only the marked-MF status of `K` and the generation
identity after adjoining a raw root.  It does not transfer MF to `E` across
that adjunction.
