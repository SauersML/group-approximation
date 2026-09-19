---
rg: 2
id: qutrit-first-nonparallel-cuntz-return-chain-is-finite
kind: claim
title: The first nonparallel Cuntz return selects a branch but remains finite
artifacts:
  - research/qutrit-nonparallel-cuntz-chain-finite-proof.md
distinct_from:
  qutrit-parallel-full-cuntz-cell-covariance-is-finite: that identifies equal central returns across parallel intermediate coordinates; this feeds such a return into the next prefix root and obtains a genuine coefficient selector.
  qutrit-first-infinite-prefix-holonomy-is-dihedral-amenable: that leaves the acyclic positive-root orientation and becomes infinite; this stays in a directed four-coordinate chain and proves the complete selector packet finite.
  positive-steinberg-qutrit-bridges-are-central-by-finite: that gives the general positive-root finiteness basin; this computes the smallest nonparallel full-Cuntz selector, its exact order, scalar intersection, and qutrit output.
---

In the `h=J^2Z`-fixed block choose a directed chain of coordinates

```text
i -> j -> k -> ell,
```

with `i,k` in trivial `C`-summands and `j,ell` corresponding
coordinates in two copies of the nontrivial `C`-type killed by `h`.
Put

```text
U_r=x_(ij)(s_r),       V_s=x_(jk)(t_s),
W_a=x_(k,ell)(s_a),            r,s,a in {0,1}.          (QNC1)
```

The first cell gives `Z_(rs)=[U_r,V_s]=x_(ik)(s_rt_s)`.
Feeding this central return into the third edge gives the exact branch
selector

```text
[Z_(rs),W_a]
 =x_(i,ell)(s_rt_ss_a)
 =delta_(sa) x_(i,ell)(s_r).                            (QNC2)
```

The other parenthesization agrees:

```text
[V_s,W_a]=delta_(sa)x_(j,ell)(1),
[U_r,[V_s,W_a]]
 =delta_(sa)x_(i,ell)(s_r).                             (QNC3)
```

Thus the full Leavitt inverse relations really delete the wrong branch
and re-emit the selected positive coefficient on a noncentral qutrit
root. This is not a parallel-cell or scalar-potential relation.

Nevertheless the generated group `M` is finite. It is `1+mathcal n`,
where the six nonzero upper-triangular coefficient spaces along the chain
have dimensions

```text
dim S=2, dim T=2, dim S=2, dim(ST)=4,
dim(TS)=1, dim(STS)=2.
```

Hence

```text
dim_(F_2)(mathcal n)=13,            |M|=2^13=8192.       (QNC4)
```

Its scalar intersection is the four-group

```text
M intersect K=<A,B>,
A=x_(ik)(1),             B=x_(j,ell)(1).                (QNC5)
```

Both `A` and `B` commute with `C`. Every root crossing a trivial and a
nontrivial coordinate, including the selected output in `(QNC2)`, has
the same complete three-by-three `h`-fibre atom graph and squared block
norm `1/27`. Therefore coefficient selection still does not orient one
qutrit character cell.

All relations `(QNC1)--(QNC3)` have the finite-vertex cover

```text
K *_(<h,A,B>) (<h> times M) -> EL_28(L).                (QNC6)
```

It is virtually free, residually finite, sofic, and hyperlinear, and its
regular microstates realize the branch deletion with uniform qutrit
weights `1/9`. Thus even the first nonparallel output-as-input relation
has no normalized-HS trace imbalance.

The obstruction is structural: every finite acyclic root-incidence
network is contained in a strictly upper-triangular group, so coefficient
word length is bounded by the number of coordinates and its generated
`F_2`-space is finite. The next eligible relation must close a directed
coordinate cycle, equivalently introduce an opposite root which feeds a
selected output back to an earlier input. Only then can repeated
coefficient words escape this finite nilpotence basin.
