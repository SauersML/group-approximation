---
rg: 2
id: degree-zero-core-dirac-haar-proof
kind: route
title: Restrict to the finite tower, expand in normalized irreducible characters, and let the dense-support ratios vanish
target: degree-zero-leavitt-core-characters-are-dirac-haar-mixtures
requires:
  - dense-support-character-ratios-of-sl-n-2-vanish
  - binary-leavitt-elementary-group-is-simple
  - torsion-normal-generator-mf-character-criterion
---

## Step 1: the tower and the support of a fixed element

`B_m=span{s_ut_v:|u|=|v|=m}~=M_(2^m)(F_2)` and `s_ut_v=sum_b s_(ub)t_(vb)`
embed `B_m` into `B_(m+1)` as `a -> a tensor 1_2`.  Hence
`G_m:=EL_n(B_m)=SL_(n*2^m)(F_2)` embeds into `G_(m+1)` as `A -> A tensor
1_2`, and `Gamma_0^(n)=union_m G_m`.  For `1!=A in G_m` and `M>=m`, the
image of `A` in `G_M=SL_N(F_2)`, `N=n*2^M`, is `A tensor 1_(2^(M-m))`.
Here support means the codimension of the largest eigenspace over the
algebraic closure.  Therefore

```text
supp(A tensor 1_(2^(M-m)))=2^(M-m) supp(A) >= 2^(M-m) = N/(n*2^m).      (1)
```

The inequality uses `supp(A)>=1`: over `F_2`, a matrix with support zero is
a scalar matrix and hence is the identity.

So the support fraction is at least `delta_m:=1/(n*2^m)`, independent of
`M`.

## Step 2: expansion of a character on a finite group

Let `phi` be a character of `Gamma_0^(n)`.  Its restriction to the finite
group `G_M` is a normalized positive-definite class function, hence

```text
phi|G_M = sum_(pi in Irr(G_M)) a_pi^(M) chi_pi/chi_pi(1),
a_pi^(M)>=0,   sum_pi a_pi^(M)=1.                                         (2)
```

The trivial weight `a_1^(M)=(1/|G_M|)sum_(g in G_M) phi(g)` equals
`<P_(G_M)xi,xi>` for the fixed-vector projection in the GNS representation
of `phi`.  Since `G_M<=G_(M+1)`, these fixed subspaces decrease and the
weights are non-increasing.  Let `w=lim_M a_1^(M)`.

## Step 3: evaluation at a fixed element

Fix `1!=A in G_m` and `M>=m`.  By `(2)` and `(1)`,

```text
|phi(A)-a_1^(M)| <= sum_(pi!=1) a_pi^(M) |chi_pi(A tensor 1)|/chi_pi(1)
                 <= sup{ |chi(g)|/chi(1) : chi!=1, supp(g)>=delta_m N },   (3)
```

and the right side tends to `0` as `M -> infinity` by
`dense-support-character-ratios-of-sl-n-2-vanish`.  Letting `M -> infinity`
gives `phi(A)=w`.  This is `(DHM2)`; the value is independent of `A` and
of `m`.

## Step 4: consequences

Item 1: a character of `H` restricts to a character of `Gamma_0^(n)`, and
MF characters are characters (pointwise limits of normalized traces of
asymptotically multiplicative unitary maps are positive definite,
normalized, and conjugation invariant).  Item 2: on the elementary abelian
group `x_ij(B_m)`, a character is the Fourier transform of a probability
measure on the dual; the measure whose transform is `1` at `0` and `w`
elsewhere is `w*delta_0+(1-w)*Haar`.  Item 3: `phi=1` on `H` forces `w=1`.
Conversely let `w=1`, so `phi(g)=1` for every `g in Gamma_0^(n)`.  In the
GNS representation of `phi` with cyclic vector `xi`, `phi(g)=1` means
`pi(g)xi=xi`; conjugation invariance gives `phi(hgh^-1)=1`, so `xi` is
fixed by every conjugate of every element of `Gamma_0^(n)`, hence by the
normal closure of `Gamma_0^(n)` in `H`, which is `H` because `H` is simple
(`binary-leavitt-elementary-group-is-simple`) and `Gamma_0^(n)!=1`.  Thus
`phi=1` on `H`.

Finally, if a corona representation of `H` is nontrivial, simplicity makes
any nonidentity involution a normal generator.  The
`torsion-normal-generator-mf-character-criterion` supplies a nontrivial MF
character; the preceding paragraph forces its parameter to satisfy `w<1`.

No Steinberg-group assertion is made here.  Passing from
`St_n(M_k(F_2))` to the flattened finite linear tower requires an additional
unstable Morita theorem and filtered-colimit compatibility.
